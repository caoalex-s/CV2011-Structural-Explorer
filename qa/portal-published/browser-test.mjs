/** One bounded public synthetic check in Linux CI; no deployment or model upload. */
import assert from 'node:assert/strict';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { resolve } from 'node:path';
import { chromium } from 'playwright';

assert.equal(process.env.GITHUB_ACTIONS, 'true');
assert.equal(process.platform, 'linux');
assert.equal(process.env.GITHUB_RUN_ATTEMPT, '1');
const [bindingPath, outputPath] = process.argv.slice(2);
const binding = JSON.parse(await readFile(bindingPath));
assert.equal(binding.approved, true);
assert.equal(binding.deployed_main, 'e36129aad36bca41a024004fa83a556257d2440b');
const root = 'https://caoalex-s.github.io/CV2011-Structural-Explorer/';
const target = root + 'portal-checker/';
assert.equal(binding.target_url, target);
const output = resolve(outputPath);
await mkdir(output, { recursive: true });
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const result = { passed: false, target, deployedMain: binding.deployed_main,
    publicationRun: binding.normal_run_id, publicationPerformed: false, requests: [], pageErrors: [] };
let browser, context, page, phase = 'before';
const inventory = page => page.evaluate(async () => (await navigator.serviceWorker.getRegistrations())
    .map(item => ({ scope: item.scope, script: item.active?.scriptURL ?? null }))
    .sort((a, b) => a.scope.localeCompare(b.scope)));
async function accepted() {
    await page.waitForFunction(() => document.getElementById('portal-status')?.textContent === 'Accepted by the compiled proved checker.');
    return JSON.parse(await page.locator('#portal-certificate').textContent());
}
try {
    browser = await chromium.launch({ headless: true });
    result.browserVersion = browser.version();
    result.browserExecutableSha256 = hash(await readFile(chromium.executablePath()));
    result.nodeVersion = process.version;
    context = await browser.newContext({ serviceWorkers: 'allow' });
    await context.tracing.start({ screenshots: true, snapshots: true, sources: false });
    context.on('request', request => result.requests.push({ phase, url: request.url(), method: request.method() }));
    page = await context.newPage();
    page.on('pageerror', error => result.pageErrors.push(error.message));
    assert.equal((await page.goto(root)).status(), 200);
    const original = await inventory(page);
    result.originalRegistrations = original;
    assert.ok(!original.some(item => item.scope === target));
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller?.scriptURL ?? null), null);
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    await page.locator('a[href="portal-checker/"]').click();
    assert.equal(page.url(), target);
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    assert.deepEqual(await inventory(page), original);
    const navigations = [];
    page.on('framenavigated', frame => { if (frame === page.mainFrame()) navigations.push(frame.url()); });
    phase = 'activation';
    await Promise.all([page.waitForNavigation({ waitUntil: 'load' }), page.locator('#portal-activate').click()]);
    const baseline = await accepted();
    assert.deepEqual(navigations, [target]);
    result.activationNavigations = [...navigations];
    assert.equal(await page.evaluate(() => crossOriginIsolated), true);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller.scriptURL), target + 'isolation-sw.js');
    assert.deepEqual((await inventory(page)).filter(item => item.scope !== target), original);
    assert.deepEqual(baseline.amplitude, { numerator: '-5', denominator: '1' });
    assert.equal(baseline.artifact, binding.wasm_sha256);
    assert.equal(baseline.bundle, binding.manifest_sha256);
    assert.match(await page.locator('#portal-readouts').textContent(), /11\.262.*-1\.720/s);
    result.baseline = baseline;

    // Reuse the production runtime and exact candidate API for the same bounded
    // out-of-order check as the accepted CI harness. Both real workers load
    // before offline mode; there is no test hook in the shipped checker.
    await page.evaluate(async () => {
        const { PortalRuntime } = await import('./portal-runtime.js');
        const candidates = await import('./portal-candidate.js');
        const runtime = new PortalRuntime();
        await runtime.ready;
        const packet = value => candidates.encodeCandidate(candidates.portalCandidate(value));
        window.portalFixture = { runtime, packet, first: await runtime.check(packet(-5)) };
    });
    result.browserAssetHashes = await page.evaluate(async names => {
        const values = {};
        for (const name of names) {
            const bytes = await (await fetch('./bundle/' + name)).arrayBuffer();
            values[name] = [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))]
                .map(byte => byte.toString(16).padStart(2, '0')).join('');
        }
        return values;
    }, ['checker.wasm', 'checker.mjs', 'checker.worker.js', 'checker.mjs.symbols']);
    for (const [name, actual] of Object.entries(result.browserAssetHashes)) {
        assert.equal(actual, binding.artifact_file_hashes['portal-checker/bundle/' + name]);
    }
    const neighbor = await context.newPage();
    assert.equal((await neighbor.goto(root + 'learn/')).status(), 200);
    assert.equal(await neighbor.evaluate(() => navigator.serviceWorker.controller?.scriptURL ?? null), null);
    assert.equal(await neighbor.evaluate(() => crossOriginIsolated), false);
    await neighbor.close();

    phase = 'offline';
    await context.setOffline(true);
    await page.locator('#portal-amplitude').fill('-12');
    const edited = await accepted();
    assert.deepEqual(edited.amplitude, { numerator: '-12', denominator: '1' });
    assert.ok(edited.request > baseline.request && edited.revision > baseline.revision);
    assert.equal(edited.artifact, binding.wasm_sha256);
    assert.equal(edited.bundle, binding.manifest_sha256);
    // Every exact response scales with this sole supported load parameter.
    for (const [name, value] of Object.entries(edited.values)) {
        const previous = baseline.values[name];
        assert.equal(BigInt(value.numerator) * BigInt(previous.denominator) * 5n,
            BigInt(previous.numerator) * BigInt(value.denominator) * 12n);
    }
    assert.match(await page.locator('#portal-readouts').textContent(), /BC midpoint moment:.*BC midpoint vertical displacement:/s);
    result.edited = edited;
    result.staleBinding = await page.evaluate(async () => {
        const { runtime, packet, first } = window.portalFixture;
        const outcomes = await Promise.all([runtime.check(packet(-5)), runtime.check(packet(-12)), runtime.check(packet(-5))]);
        const staleRejected = !runtime.receive(first);
        runtime.dispose();
        return { outcomes: outcomes.map(value => value.state), staleRejected };
    });
    assert.deepEqual(result.staleBinding, { outcomes: ['stale', 'stale', 'accepted'], staleRejected: true });
    for (const value of ['-7', '-12', '-5']) await page.locator('#portal-amplitude').fill(value);
    const reverted = await accepted();
    assert.deepEqual(reverted.amplitude, baseline.amplitude);
    assert.ok(reverted.request > edited.request && reverted.revision > edited.revision);
    result.reverted = reverted;
    result.offlineRequests = result.requests.filter(item => item.phase === 'offline');
    assert.deepEqual(result.offlineRequests, []);
    await page.screenshot({ path: resolve(output, 'published-portal.png'), fullPage: true });

    phase = 'cleanup';
    await context.setOffline(false);
    await Promise.all([page.waitForURL(root), page.locator('#portal-deactivate').click()]);
    assert.deepEqual(await inventory(page), original);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller?.scriptURL ?? null), null);
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    await page.goto(target);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller?.scriptURL ?? null), null);
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    assert.deepEqual(await inventory(page), original);
    result.cleanup = 'Exact checker scope removed; original registration inventory restored; root and neighboring Learn page unaffected.';
    await page.goto(root + 'learn/');
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller?.scriptURL ?? null), null);
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    assert.deepEqual(await inventory(page), original);
    assert.deepEqual(result.pageErrors, []);
    result.passed = true;
} catch (error) {
    result.failure = { phase, message: error.message, stack: error.stack };
    throw error;
} finally {
    if (context) {
        await context.setOffline(false);
        const current = context.pages().find(item => item.url().startsWith(root));
        if (current) {
            try {
                result.failureCleanup = await current.evaluate(async scope => {
                    window.portalFixture?.runtime.dispose();
                    const exact = (await navigator.serviceWorker.getRegistrations()).find(item => item.scope === scope &&
                        [item.active, item.waiting, item.installing].some(worker => worker?.scriptURL === scope + 'isolation-sw.js'));
                    return exact ? await exact.unregister() : 'not registered';
                }, target);
            } catch (error) { result.cleanupError = error.message; }
        }
        await context.tracing.stop({ path: resolve(output, 'published-portal-trace.zip') });
    }
    await writeFile(resolve(output, 'published-portal-result.json'), JSON.stringify(result, null, 2) + '\n');
    await browser?.close();
}
