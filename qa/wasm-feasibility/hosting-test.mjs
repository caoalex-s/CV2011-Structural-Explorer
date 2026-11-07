/** CI-only headerless static-subpath experiment. No production registration. */
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { readFile, writeFile } from 'node:fs/promises';
import { resolve } from 'node:path';
import { createHash } from 'node:crypto';
import { chromium } from 'playwright';

const [assets, sources, output] = process.argv.slice(2).map(path => resolve(path));
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const pin = JSON.parse(await readFile(resolve(sources, 'hosting-source.json')));
const prefix = pin.scope_path;
const html = '<!doctype html><title>Synthetic isolation diagnostic</title><link rel="icon" href="data:,"><output>cold</output>';
const files = new Map([[prefix + 'index.html', { data: Buffer.from(html), type: 'text/html' }]]);
const outsidePath = '/CV2011-Structural-Explorer/outside.html';
files.set(outsidePath, { data: Buffer.from(html), type: 'text/html' });
for (const [url, file] of [['isolation-sw.js', 'isolation-sw.js'],
    ['harness.mjs', 'hosting-harness.mjs'], ['worker.mjs', 'hosting-worker.mjs']]) {
    files.set(prefix + url, { data: await readFile(resolve(sources, file)), type: 'text/javascript' });
}
const manifest = {};
for (const [name, expected] of Object.entries(pin.final_assets)) {
    const data = await readFile(resolve(assets, name));
    assert.equal(hash(data), expected.sha256);
    assert.equal(data.length, expected.bytes);
    manifest[name] = hash(data);
    files.set(prefix + name, { data, type: name.endsWith('.wasm') ? 'application/wasm' : 'text/javascript' });
}
assert.equal(hash(files.get(prefix + 'isolation-sw.js').data), pin.shim_sha256);
let phase = 'native-probe';
let offline = false;
let tamperedManifest = false;
const serverTrace = [];
// This server deliberately never sends COOP, COEP, CORP or Service-Worker-Allowed.
const server = createServer((request, response) => {
    const path = new URL(request.url, 'http://localhost').pathname;
    let file = files.get(path);
    if (path === prefix + 'manifest.json') {
        const advertised = { ...manifest };
        if (tamperedManifest) advertised['checker.wasm'] = '0'.repeat(64);
        file = { data: Buffer.from(JSON.stringify(advertised)), type: 'application/json' };
    }
    const status = offline ? 503 : file ? 200 : 404;
    response.setHeader('Cache-Control', 'no-store');
    if (file) response.setHeader('Content-Type', file.type);
    serverTrace.push({ phase, url: request.url, status, headers: response.getHeaders(),
        payloadSha256: status === 200 ? hash(file.data) : null });
    response.writeHead(status).end(status === 200 ? file.data : 'unavailable');
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const origin = `http://127.0.0.1:${server.address().port}`;
const scopeURL = origin + prefix;
const pageURL = scopeURL + 'index.html';
const result = { passed: false, stage: phase, artifact: pin.final_assets,
    shimSha256: pin.shim_sha256, scopeURL, nativeHeaders: [], lifecycle: {}, serverTrace,
    responseTrace: [], pageErrors: [], noPublicDeployment: true };
let browser;
let context;
const responseTasks = [];

try {
    // Node's native HTTP fetch bypasses service workers and browser request routing.
    for (const path of ['index.html', 'isolation-sw.js', 'checker.wasm', 'checker.mjs', 'checker.worker.js']) {
        const response = await fetch(scopeURL + path);
        const headers = Object.fromEntries(response.headers);
        for (const name of ['cross-origin-opener-policy', 'cross-origin-embedder-policy',
            'cross-origin-resource-policy', 'service-worker-allowed']) assert.equal(headers[name], undefined);
        assert.equal(response.status, 200);
        result.nativeHeaders.push({ url: response.url, headers, sha256: hash(Buffer.from(await response.arrayBuffer())) });
    }
    browser = await chromium.launch({ headless: true });
    result.browserVersion = browser.version();
    result.browserExecutableSha256 = hash(await readFile(chromium.executablePath()));
    context = await browser.newContext({ serviceWorkers: 'allow' });
    await context.tracing.start({ screenshots: false, snapshots: true, sources: false });
    const page = await context.newPage();
    page.on('pageerror', error => result.pageErrors.push(error.message));
    page.on('response', response => {
        responseTasks.push(response.allHeaders().then(headers => result.responseTrace.push({
            url: response.url(), status: response.status(), fromServiceWorker: response.fromServiceWorker(), headers,
        })));
    });
    const navigations = [];
    page.on('framenavigated', frame => { if (frame === page.mainFrame()) navigations.push(frame.url()); });
    const state = () => page.evaluate(async () => ({ isolated: crossOriginIsolated,
        sharedArrayBuffer: typeof SharedArrayBuffer, secure: isSecureContext,
        controller: navigator.serviceWorker.controller?.scriptURL ?? null,
        scopes: (await navigator.serviceWorker.getRegistrations()).map(registration => registration.scope) }));

    phase = result.stage = 'cold-install';
    const coldResponse = await page.goto(pageURL);
    result.lifecycle.cold = await state();
    assert.equal(coldResponse.fromServiceWorker(), false);
    assert.equal(result.lifecycle.cold.isolated, false);
    assert.equal(result.lifecycle.cold.sharedArrayBuffer, 'undefined');
    assert.equal(result.lifecycle.cold.secure, true);
    assert.equal(result.lifecycle.cold.controller, null);
    assert.deepEqual(result.lifecycle.cold.scopes, []);
    await page.evaluate(async () => {
        await navigator.serviceWorker.register(new URL('./isolation-sw.js', location.href),
            { scope: './', updateViaCache: 'none' });
        await navigator.serviceWorker.ready;
    });
    await page.waitForFunction(() => navigator.serviceWorker.controller !== null);
    result.lifecycle.claimedBeforeReload = await state();
    assert.equal(result.lifecycle.claimedBeforeReload.controller, scopeURL + 'isolation-sw.js');
    phase = result.stage = 'one-controlled-reload';
    const isolatedResponse = await page.reload();
    result.lifecycle.isolated = await state();
    assert.equal(isolatedResponse.fromServiceWorker(), true);
    assert.equal(result.lifecycle.isolated.isolated, true);
    assert.equal(result.lifecycle.isolated.sharedArrayBuffer, 'function');
    assert.deepEqual(result.lifecycle.isolated.scopes, [scopeURL]);
    const controlledHeaders = await isolatedResponse.allHeaders();
    assert.equal(controlledHeaders['cross-origin-opener-policy'], 'same-origin');
    assert.equal(controlledHeaders['cross-origin-embedder-policy'], 'require-corp');
    result.lifecycle.controlledHeaders = controlledHeaders;
    assert.equal(navigations.length, 2, 'Only cold navigation and one explicit reload are allowed');

    // Verify that neighboring content is neither controlled nor rewritten.
    phase = result.stage = 'scope-and-immutable-update';
    const outside = await context.newPage();
    await outside.goto(origin + outsidePath);
    result.lifecycle.outside = await outside.evaluate(() => ({ isolated: crossOriginIsolated,
        controller: navigator.serviceWorker.controller?.scriptURL ?? null }));
    assert.deepEqual(result.lifecycle.outside, { isolated: false, controller: null });
    await outside.close();
    result.lifecycle.outsideFetch = await page.evaluate(async path => {
        const response = await fetch(path);
        return { coop: response.headers.get('Cross-Origin-Opener-Policy'),
            coep: response.headers.get('Cross-Origin-Embedder-Policy') };
    }, origin + outsidePath);
    assert.deepEqual(result.lifecycle.outsideFetch, { coop: null, coep: null });
    result.lifecycle.sameByteUpdate = await page.evaluate(async () => {
        const registration = await navigator.serviceWorker.getRegistration();
        await registration.update(); // Explicit same-script diagnostic, never a scheduled updater.
        return { scope: registration.scope, active: registration.active.scriptURL,
            installing: registration.installing !== null, waiting: registration.waiting !== null };
    });
    assert.deepEqual(result.lifecycle.sameByteUpdate, { scope: scopeURL,
        active: scopeURL + 'isolation-sw.js', installing: false, waiting: false });
    assert.equal(navigations.length, 2, 'No update-triggered reload');

    phase = result.stage = 'browser-byte-integrity';
    result.browserAssetHashes = await page.evaluate(async names => {
        const hashes = {};
        for (const name of names) {
            const bytes = await (await fetch(new URL(name, location.href))).arrayBuffer();
            hashes[name] = Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256', bytes)))
                .map(byte => byte.toString(16).padStart(2, '0')).join('');
        }
        return hashes;
    }, Object.keys(manifest));
    assert.deepEqual(result.browserAssetHashes, manifest);
    tamperedManifest = true;
    result.integrityFailure = await page.evaluate(() => new Promise((resolve, reject) => {
        const probe = new Worker(new URL('./worker.mjs?integrity-probe', location.href), { type: 'module' });
        const timer = setTimeout(() => { probe.terminate(); reject(new Error('Integrity probe timeout')); }, 15000);
        probe.onmessage = () => { clearTimeout(timer); probe.terminate(); reject(new Error('Tampered manifest initialized')); };
        probe.onerror = error => { error.preventDefault(); clearTimeout(timer); probe.terminate(); resolve(error.message); };
    }));
    assert.match(result.integrityFailure, /Artifact digest mismatch/);
    tamperedManifest = false;
    result.initialization = await page.evaluate(async () => {
        const { Checker } = await import(new URL('./harness.mjs', location.href).href);
        window.Checker = Checker;
        window.checker = new Checker();
        return await checker.ready;
    });
    assert.equal(result.initialization.artifact, manifest['checker.wasm']);
    assert.equal(result.initialization.isolated, true);
    assert.equal(result.initialization.sharedArrayBuffer, 'function');

    phase = result.stage = 'offline-compiled-checker';
    offline = true;
    await context.setOffline(true);
    // FUNCTIONAL_CASES: same accepted rational, ABI, request-binding and timeout checks.
    const large = '123456789012345678901234567890123456789012345678901234567890';
    const cases = [
        ['zero', '0\n1\n0\n7', 'accepted'],
        ['positive', '10\n1\n5\n1', 'accepted'],
        ['negative', '-10\n1\n-5\n1', 'accepted'],
        ['fraction', '3\n7\n3\n14', 'accepted'],
        ['unreduced', '6\n14\n9\n42', 'accepted'],
        ['large-integer', `${large}\n1\n${large}\n2`, 'accepted'],
        ['large-fraction', `${large}\n7\n${large}\n14`, 'accepted'],
        ['wrong-sign', '-10\n1\n5\n1', 'rejected'],
        ['wrong-value', '10\n1\n6\n1', 'rejected'],
        ['tampered-denominator', '3\n7\n3\n15', 'rejected'],
        ['zero-denominator', '0\n0\n0\n1', 'malformed'],
        ['negative-denominator', '1\n-1\n1\n2', 'malformed'],
        ['negative-zero', '-0\n1\n0\n1', 'malformed'],
        ['leading-zero', '01\n1\n1\n2', 'malformed'],
        ['plus', '+1\n1\n1\n2', 'malformed'],
        ['missing', '1\n1\n1', 'malformed'],
        ['extra', '1\n1\n1\n2\n1', 'malformed'],
        ['truncated', '1\n1\n1\n', 'malformed'],
        ['NUL', '1\n1\n1\n2\0', 'malformed'],
        ['digits-limit', `${'9'.repeat(129)}\n1\n1\n1`, 'limit'],
        ['payload-limit', '1'.repeat(4097), 'limit'],
    ];
    const results = [];
    for (const [name, input, expected] of cases) {
        const result = await page.evaluate(input => checker.check(input), input);
        assert.equal(result.state, expected, name);
        results.push({ name, inputSha256: hash(input), expected, result });
    }
    const abiCases = await page.evaluate(async () => [
        await checker.check(new Uint8Array([0xc0, 0x80, 10, 49, 10, 49, 10, 50])),
        await checker.check('2\n1\n1\n1', { pointerOffset: 1 }),
        await checker.check('2\n1\n1\n1', { length: 0xffffffff }),
        await checker.check('2\n1\n1\n1', { length: 0 }),
    ]);
    assert.deepEqual(abiCases.map(result => result.state), ['malformed', 'malformed', 'limit', 'malformed']);
    const binding = await page.evaluate(async () => {
        const old = checker.state;
        const pending = checker.check('14\n1\n7\n1');
        const staleRejected = !checker.receive(old);
        const tamperRejected = !checker.receive({ ...old, id: checker.revision, artifact: 'tampered' });
        const result = await pending;
        const rapid = await Promise.all([checker.check('10\n1\n5\n1'),
            checker.check('12\n1\n6\n1'), checker.check('10\n1\n5\n1')]);
        return { staleRejected, tamperRejected, result, rapid, final: checker.state };
    });
    assert.ok(binding.staleRejected && binding.tamperRejected);
    assert.deepEqual(binding.rapid.map(result => result.state), ['stale', 'stale', 'accepted']);
    const timing = await page.evaluate(async () => {
        const milliseconds = [];
        for (let i = 0; i < 100; i++) {
            const result = await checker.check(i % 2 ? '10\n1\n5\n1' : '-10\n1\n-5\n1');
            if (result.state !== 'accepted') throw new Error('Repeated input failed');
            milliseconds.push(result.milliseconds);
        }
        return milliseconds;
    });
    const timeout = await page.evaluate(() => checker.check('10\n1\n5\n1', { stall: true }));
    assert.equal(timeout.state, 'timeout');
    assert.equal(await page.locator('output').textContent(), JSON.stringify(timeout));
    assert.equal(serverTrace.filter(item => item.phase === phase).length, 0);
    assert.deepEqual(result.pageErrors, []);
    Object.assign(result, { cases: results, abiCases, binding, offlineChecks: timing.length, timeout });


    phase = result.stage = 'reset-and-unregister';
    offline = false;
    await context.setOffline(false);
    result.lifecycle.reset = await page.evaluate(async () => {
        const stale = checker.state;
        checker.worker.terminate();
        window.checker = new Checker();
        const initialized = await checker.ready;
        const staleRejected = !checker.receive(stale);
        const checked = await checker.check('10\n1\n5\n1');
        checker.worker.terminate();
        return { initialized, staleRejected, checked };
    });
    assert.equal(result.lifecycle.reset.initialized.artifact, manifest['checker.wasm']);
    assert.equal(result.lifecycle.reset.staleRejected, true);
    assert.equal(result.lifecycle.reset.checked.state, 'accepted');
    assert.equal(navigations.length, 2, 'No unrequested navigation before explicit reset');
    result.lifecycle.navigationsBeforeUnregister = [...navigations];
    result.lifecycle.unregistered = await page.evaluate(async () => {
        const registrations = await navigator.serviceWorker.getRegistrations();
        return await Promise.all(registrations.map(registration => registration.unregister()));
    });
    assert.deepEqual(result.lifecycle.unregistered, [true]);
    // Release the old controlled client before testing a fresh navigation.
    await page.goto(origin + outsidePath);
    const resetResponse = await page.goto(pageURL + '?reset=1');
    result.lifecycle.afterUnregister = await state();
    assert.equal(resetResponse.fromServiceWorker(), false);
    assert.equal(result.lifecycle.afterUnregister.isolated, false);
    assert.equal(result.lifecycle.afterUnregister.sharedArrayBuffer, 'undefined');
    assert.equal(result.lifecycle.afterUnregister.controller, null);
    assert.deepEqual(result.lifecycle.afterUnregister.scopes, []);
    assert.deepEqual(await page.evaluate(() => caches.keys()), []);
    assert.deepEqual(result.pageErrors, []);
    for (const entry of serverTrace) {
        assert.ok(entry.url.startsWith(prefix) || entry.url === outsidePath, entry.url);
        assert.equal(entry.headers['cross-origin-opener-policy'], undefined);
        assert.equal(entry.headers['cross-origin-embedder-policy'], undefined);
    }
    result.passed = true;
    result.stage = 'complete';
} catch (error) {
    result.failure = { message: error.message, stack: error.stack };
    throw error;
} finally {
    await Promise.all(responseTasks);
    if (context) await context.tracing.stop({ path: resolve(output, 'browser-trace.zip') });
    await writeFile(resolve(output, 'hosting-results.json'), JSON.stringify(result, null, 2) + '\n');
    if (browser) await browser.close();
    await new Promise(resolve => server.close(resolve));
}
