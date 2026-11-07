/** Actual pinned Chromium test. Run only in the synthetic Linux CI job.
 * JavaScript supplies strings and checks statuses; Lean performs the arithmetic. */
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { readFile, writeFile, stat } from 'node:fs/promises';
import { resolve, basename, dirname } from 'node:path';
import { createHash } from 'node:crypto';
import { chromium } from 'playwright';

const [assets, sources] = process.argv.slice(2).map(path => resolve(path));
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const manifest = {};
const payloadBytes = {};
for (const name of ['checker.wasm', 'checker.mjs']) {
    const bytes = await readFile(resolve(assets, name));
    manifest[name] = hash(bytes);
    payloadBytes[name] = bytes.length;
}
const requests = [];
let offline = false;
const server = createServer(async (request, response) => {
    requests.push({ url: request.url, afterInitialization: offline });
    response.setHeader('Cross-Origin-Opener-Policy', 'same-origin');
    response.setHeader('Cross-Origin-Embedder-Policy', 'require-corp');
    response.setHeader('Cache-Control', 'no-store');
    if (offline) { response.writeHead(503).end(); return; }
    try {
        const name = basename(new URL(request.url, 'http://localhost').pathname);
        if (!name) {
            response.setHeader('Content-Type', 'text/html');
            response.end('<!doctype html><title>Synthetic rational checker gate</title><output>initializing</output>');
        } else if (name === 'manifest.json') {
            response.setHeader('Content-Type', 'application/json');
            response.end(JSON.stringify(manifest));
        } else {
            const directory = ['worker.mjs', 'harness.mjs'].includes(name) ? sources : assets;
            response.setHeader('Content-Type', name.endsWith('.wasm') ? 'application/wasm' : 'text/javascript');
            response.end(await readFile(resolve(directory, name)));
        }
    } catch { response.writeHead(404).end(); }
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const browser = await chromium.launch({ headless: true });
const context = await browser.newContext({ serviceWorkers: 'block' });
const page = await context.newPage();
const pageErrors = [];
page.on('pageerror', error => pageErrors.push(error.message));
const blockedRequests = [];
try {
    const start = performance.now();
    await page.goto(`http://127.0.0.1:${server.address().port}/`);
    const initialization = await page.evaluate(async () => {
        const { Checker } = await import('/harness.mjs');
        window.checker = new Checker();
        return await window.checker.ready;
    });
    const startupMilliseconds = performance.now() - start;
    // Refuse every later request at the browser and at the local asset server.
    // The server is only a static CI harness; there is no checking endpoint.
    offline = true;
    await context.route('**/*', route => { blockedRequests.push(route.request().url()); return route.abort(); });
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
    assert.equal(blockedRequests.length, 0);
    assert.equal(requests.filter(item => item.afterInitialization).length, 0);
    assert.deepEqual(pageErrors, []);
    const executable = chromium.executablePath();
    const result = { passed: true, browserVersion: browser.version(),
        browserExecutableSha256: hash(await readFile(executable)),
        browserExecutableBytes: (await stat(executable)).size,
        artifact: manifest, payloadBytes, startupMilliseconds, initialization,
        memoryCeilingBytes: 134217728, requestTimeoutMilliseconds: 1000,
        latencyMethod: 'performance.now around only the compiled ABI call in the worker; 100 alternating signed checks after functional cases; no network; milliseconds are timer-resolution limited',
        steadyStateMilliseconds: timing, cases: results, abiCases, binding, timeout,
        blockedRequests, requests, pageErrors };
    await writeFile(resolve(dirname(assets), 'browser-results.json'), JSON.stringify(result, null, 2) + '\n');
} finally {
    await browser.close();
    server.close();
}
