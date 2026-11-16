/** Bounded Linux CI smoke of the normal Pages artifact on the public main UI. */
import assert from 'node:assert/strict';
import { readFile, writeFile, mkdir, copyFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { chromium } from 'playwright';

assert.equal(process.platform, 'linux');
assert.equal(process.env.GITHUB_ACTIONS, 'true');
const root = 'https://caoalex-s.github.io/CV2011-Structural-Explorer/';
const output = resolve('.data/published-inclined');
await mkdir(output, { recursive: true });
const binding = JSON.parse(await readFile(resolve(output, 'live-binding-before.json')));
assert.equal(binding.commit, process.env.GITHUB_SHA);
const manifestBytes = await readFile('public/portal-checker/bundle/manifest.json');
const manifest = JSON.parse(manifestBytes);
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const result = { passed: false, publicationPerformed: false, deployedCommit: binding.commit,
    artifact: manifest.files['checker.wasm'], bundle: hash(manifestBytes), cases: [], errors: [], responses: {} };

// Only synthetic fixtures enter this new browser context. They are imported
// into local application state and never submitted to an external endpoint.
await mkdir('.data/live-portal/inclined-native', { recursive: true });
for (const name of ['cantilever-interior.request.json', 'cantilever-interior.report'])
    await copyFile('qa/inclined-frame/published-fixtures/' + name, '.data/live-portal/inclined-native/' + name);
const browser = await chromium.launch({ headless: true });
const context = await browser.newContext({ acceptDownloads: true, viewport: { width: 1440, height: 1000 } });
const pendingResponses = [];
await context.route('**/*', async route => {
    const request = route.request();
    if (!request.url().startsWith(root) || request.method() !== 'GET') {
        result.errors.push('Unexpected request: ' + request.method() + ' ' + request.url());
        await route.abort();
    } else await route.continue();
});
context.on('response', response => {
    const url = new URL(response.url());
    const relative = url.pathname.slice(new URL(root).pathname.length);
    if (binding.files[relative]) pendingResponses.push((async () => {
        const actual = hash(await response.body());
        assert.equal(actual, binding.files[relative], relative);
        result.responses[relative] = actual;
    })());
});
const page = await context.newPage();
page.on('pageerror', error => result.errors.push(String(error)));
await context.tracing.start({ screenshots: true, snapshots: true });
try {
    await page.goto(root);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller), null);
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    assert.equal(await page.evaluate(async () => (await navigator.serviceWorker.getRegistrations()).length), 0);
    result.coldActivationVerified = true;
    const { runMainInclinedCases } = await import(pathToFileURL(resolve('qa/inclined-frame/main-browser-cases.mjs')));
    await runMainInclinedCases({ page, context, output, origin: new URL(root).origin,
        base: new URL(root).pathname, result });
    await Promise.all(pendingResponses);
    for (const name of ['portal-live.js', 'portal-runtime.js', 'frame-interval-display.js', 'frame-interval-worked.js'])
        assert.equal(result.responses[name], binding.files[name], 'Actual browser source: ' + name);
    assert.deepEqual(result.errors, []);
    assert.equal(result.mainInclined.verified, true);
    result.passed = true;
} catch (error) {
    result.failure = String(error.stack ?? error);
    throw error;
} finally {
    await context.tracing.stop({ path: resolve(output, 'published-main-trace.zip') });
    await writeFile(resolve(output, 'published-main-results.json'), JSON.stringify(result, null, 2) + '\n');
    await browser.close();
}
