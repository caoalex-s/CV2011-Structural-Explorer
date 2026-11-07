/** PREPARATION ONLY. One approved Linux CI browser test; never deploys files. */
import assert from 'node:assert/strict';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { resolve } from 'node:path';

const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const [lockPath, approvalPath, outputPath] = process.argv.slice(2);
assert.equal(process.env.GITHUB_ACTIONS, 'true', 'Approved Linux CI only');
assert.equal(process.platform, 'linux');
const lockBytes = await readFile(lockPath);
const lock = JSON.parse(lockBytes);
const approval = JSON.parse(await readFile(approvalPath));
assert.equal(approval.approved, true, 'Explicit user publication and one-test approval is required');
assert.equal(approval.candidate_commit, lock.candidate_commit);
assert.equal(approval.target_url, lock.target_url);
assert.equal(approval.lock_sha256, hash(lockBytes));
assert.ok(typeof approval.human_approval_reference === 'string' && approval.human_approval_reference.trim().length > 0);
assert.equal(lock.target_url, 'https://caoalex-s.github.io/CV2011-Structural-Explorer/checker-preview/64b31158/');
const { chromium } = await import('playwright');
const output = resolve(outputPath);
await mkdir(output, { recursive: true });
const rootURL = 'https://caoalex-s.github.io/CV2011-Structural-Explorer/';
const result = { passed: false, candidate: lock.candidate_commit, target: lock.target_url,
    native: [], requests: [], responses: [], pageErrors: [], publicationPerformed: false };
const headerTasks = [];
let context;
let browser;
let phase = 'native-cdn-bytes';

async function nativeFile(url, expectedHash, mimeTypes) {
    const response = await fetch(url, { redirect: 'error', cache: 'no-store' });
    const headers = Object.fromEntries(response.headers);
    const bytes = Buffer.from(await response.arrayBuffer());
    result.native.push({ url, status: response.status, headers, sha256: hash(bytes), bytes: bytes.length });
    assert.equal(response.status, 200, url);
    assert.equal(hash(bytes), expectedHash, url);
    assert.ok(mimeTypes.includes((headers['content-type'] ?? '').split(';')[0].trim()), url);
    return headers;
}

async function inventory(page) {
    return await page.evaluate(async () => (await navigator.serviceWorker.getRegistrations())
        .map(item => ({ scope: item.scope, script: item.active?.scriptURL ?? null }))
        .sort((a, b) => a.scope.localeCompare(b.scope)));
}

try {
    // Native fetch is outside the browser and cannot be rewritten by a service worker.
    for (const [name, file] of Object.entries(lock.files)) {
        const headers = await nativeFile(new URL(name, lock.target_url), file.sha256, file.mime);
        assert.equal(headers['cross-origin-opener-policy'], undefined);
        assert.equal(headers['cross-origin-embedder-policy'], undefined);
        assert.equal(headers['service-worker-allowed'], undefined);
    }
    await nativeFile(rootURL + 'index.html', lock.baseline_index_sha256, ['text/html']);
    browser = await chromium.launch({ headless: true });
    result.browserVersion = browser.version();
    result.browserExecutableSha256 = hash(await readFile(chromium.executablePath()));
    context = await browser.newContext({ serviceWorkers: 'allow' });
    await context.tracing.start({ screenshots: true, snapshots: true, sources: false });
    context.on('request', request => result.requests.push({ phase, url: request.url(), method: request.method() }));
    const page = await context.newPage();
    page.on('pageerror', error => result.pageErrors.push(error.message));
    page.on('response', response => headerTasks.push(response.allHeaders().then(headers =>
        result.responses.push({ url: response.url(), headers, fromServiceWorker: response.fromServiceWorker() }))));
    phase = 'neighbor-before';
    await page.goto(rootURL);
    const originalRegistrations = await inventory(page);
    result.originalRegistrations = originalRegistrations;
    assert.ok(!originalRegistrations.some(item => item.scope === lock.target_url));
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller?.scriptURL ?? null), null);

    phase = 'cold-preview';
    await page.goto(lock.target_url + 'index.html');
    const navigationCount = [];
    page.on('framenavigated', frame => { if (frame === page.mainFrame()) navigationCount.push(frame.url()); });
    result.cold = await page.evaluate(() => ({ isolated: crossOriginIsolated, sab: typeof SharedArrayBuffer,
        controller: navigator.serviceWorker.controller?.scriptURL ?? null }));
    assert.deepEqual(result.cold, { isolated: false, sab: 'undefined', controller: null });
    assert.deepEqual(await inventory(page), originalRegistrations);
    assert.equal(result.requests.filter(item => item.phase === phase && item.url.endsWith('/checker.wasm')).length, 0);
    assert.equal(await page.locator('#check').isDisabled(), true);

    phase = 'explicit-activation';
    await Promise.all([page.waitForNavigation({ waitUntil: 'load' }), page.locator('#activate').click()]);
    await page.waitForFunction(() => document.querySelector('#status').textContent.startsWith('Ready.'));
    assert.deepEqual(navigationCount, [lock.target_url + 'index.html']);
    result.ready = await page.evaluate(async () => {
        const { preview } = await import('./preview.mjs');
        return { pageIsolated: crossOriginIsolated, sab: typeof SharedArrayBuffer,
            controller: navigator.serviceWorker.controller.scriptURL, worker: await preview.checker.ready };
    });
    assert.equal(result.ready.pageIsolated, true);
    assert.equal(result.ready.sab, 'function');
    assert.equal(result.ready.controller, lock.target_url + 'isolation-sw.js');
    assert.equal(result.ready.worker.isolated, true);
    assert.equal(result.ready.worker.sharedArrayBuffer, 'function');
    assert.equal(result.ready.worker.artifact, lock.files['checker.wasm'].sha256);
    const registrations = await inventory(page);
    assert.deepEqual(registrations.filter(item => item.scope !== lock.target_url), originalRegistrations);
    assert.equal(registrations.filter(item => item.scope === lock.target_url).length, 1);
    result.browserAssetHashes = await page.evaluate(async names => {
        const hashes = {};
        for (const name of names) {
            const bytes = await (await fetch(new URL(name, location.href))).arrayBuffer();
            hashes[name] = Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256', bytes)))
                .map(byte => byte.toString(16).padStart(2, '0')).join('');
        }
        return hashes;
    }, ['checker.wasm', 'checker.mjs', 'checker.worker.js', 'checker.mjs.symbols']);
    for (const [name, actual] of Object.entries(result.browserAssetHashes)) assert.equal(actual, lock.files[name].sha256);
    const neighbor = await context.newPage();
    await neighbor.goto(rootURL);
    assert.equal(await neighbor.evaluate(() => navigator.serviceWorker.controller?.scriptURL ?? null), null);
    await neighbor.close();

    phase = 'offline';
    await context.setOffline(true);
    await page.locator('#example').selectOption('wrong');
    await page.locator('#check').click();
    await page.waitForFunction(() => document.querySelector('output').textContent.startsWith('Rejected:'));
    result.cases = await page.evaluate(async () => {
        const { preview, examples } = await import('./preview.mjs');
        const states = {};
        for (const [name, input] of Object.entries(examples)) states[name] = (await preview.checker.check(input)).state;
        return states;
    });
    assert.deepEqual(result.cases, { zero: 'accepted', positive: 'accepted', negative: 'accepted',
        fraction: 'accepted', large: 'accepted', wrong: 'rejected', malformed: 'malformed' });
    result.binding = await page.evaluate(async () => {
        const { preview, examples } = await import('./preview.mjs');
        const checker = preview.checker;
        const previous = checker.state;
        const rapid = await Promise.all([checker.check(examples.positive), checker.check(examples.negative), checker.check(examples.positive)]);
        const staleRejected = !checker.receive(previous);
        for (let count = 0; count < 100; count++) {
            if ((await checker.check(count % 2 ? examples.positive : examples.negative)).state !== 'accepted') throw new Error('Offline repeat failed');
        }
        return { rapid: rapid.map(item => item.state), staleRejected,
            timeout: await checker.check(examples.positive, { stall: true }) };
    });
    assert.deepEqual(result.binding.rapid, ['stale', 'stale', 'accepted']);
    assert.equal(result.binding.staleRejected, true);
    assert.equal(result.binding.timeout.state, 'timeout');
    assert.equal(result.requests.filter(item => item.phase === 'offline').length, 0);

    phase = 'reset';
    await context.setOffline(false);
    await page.locator('#reset').click();
    result.reset = await page.evaluate(async () => {
        const { preview, examples } = await import('./preview.mjs');
        await preview.checker.ready;
        return await preview.checker.check(examples.positive);
    });
    assert.equal(result.reset.state, 'accepted');
    phase = 'exact-scope-deactivation';
    await Promise.all([page.waitForURL(rootURL), page.locator('#deactivate').click()]);
    assert.deepEqual(await inventory(page), originalRegistrations);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller?.scriptURL ?? null), null);
    await page.goto(lock.target_url + 'index.html');
    result.afterDeactivate = await page.evaluate(() => ({ isolated: crossOriginIsolated,
        controller: navigator.serviceWorker.controller?.scriptURL ?? null }));
    assert.deepEqual(result.afterDeactivate, { isolated: false, controller: null });
    assert.deepEqual(await inventory(page), originalRegistrations);
    await nativeFile(rootURL + 'index.html', lock.baseline_index_sha256, ['text/html']);
    assert.deepEqual(result.pageErrors, []);
    result.passed = true;
} catch (error) {
    result.failure = { phase, message: error.message, stack: error.stack };
    throw error;
} finally {
    // On failure, only the named preview registration may be removed.
    if (context) {
        const page = context.pages().find(page => page.url().startsWith(lock.target_url));
        if (page) {
            try {
                result.failureCleanup = await page.evaluate(async scope => {
                    const exact = (await navigator.serviceWorker.getRegistrations()).find(item => item.scope === scope);
                    return exact ? await exact.unregister() : 'not registered';
                }, lock.target_url);
            } catch (error) { result.cleanupError = error.message; }
        }
        await Promise.all(headerTasks);
        await context.tracing.stop({ path: resolve(output, 'public-preview-trace.zip') });
    }
    await writeFile(resolve(output, 'public-preview-result.json'), JSON.stringify(result, null, 2) + '\n');
    if (browser) await browser.close(); // Releases only this fresh CI context's clients.
}
