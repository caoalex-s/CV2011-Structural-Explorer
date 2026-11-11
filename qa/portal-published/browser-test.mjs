/** One bounded public synthetic check in Linux CI; no deployment or model upload. */
import assert from 'node:assert/strict';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { resolve } from 'node:path';

/** Hash navigation keeps document identity; an activation must replace it once. */
function assertActivation(before, after, documents, frameUrls, target) {
    const routed = target + '#sandbox';
    assert.equal(before.url, routed);
    assert.equal(after.url, routed);
    assert.notEqual(after.id, before.id, 'Activation must replace the document.');
    assert.ok(after.timeOrigin > before.timeOrigin);
    assert.equal(after.navigationType, 'reload');
    assert.equal(documents.length, 1, 'Exactly one new document is allowed until deactivation.');
    assert.equal(documents[0].id, after.id);
    assert.equal(documents[0].timeOrigin, after.timeOrigin);
    assert.ok([target, routed].includes(documents[0].url));
    assert.ok(frameUrls.length >= 1);
    for (const url of frameUrls) assert.ok([target, routed].includes(url), 'Unexpected activation route.');
}

// Pure fixtures exercise the actual assertion without loading Playwright or a runtime.
if (process.argv[2] === '--assertion-fixtures') {
    const target = 'https://example.test/portal-checker/';
    const before = { id: 'cold', timeOrigin: 100, url: target + '#sandbox' };
    const after = { id: 'active', timeOrigin: 200, url: before.url, navigationType: 'reload' };
    const documents = [{ id: after.id, timeOrigin: after.timeOrigin, url: after.url }];
    assertActivation(before, after, documents, [after.url, after.url], target);
    assert.throws(() => assertActivation(before, { ...after, id: before.id }, [], [after.url], target));
    assert.throws(() => assertActivation(before, after, [...documents, { ...documents[0], id: 'loop' }], [after.url], target));
    assert.throws(() => assertActivation(before, { ...after, navigationType: 'navigate' }, documents, [after.url], target));
    assert.throws(() => assertActivation(before, after, documents, [target + '?wrong=1#sandbox'], target));
    assert.throws(() => assertActivation(before, { ...after, url: target + '#practice' }, documents, [after.url], target));
    assert.throws(() => assertActivation(before, after, [{ ...documents[0], id: 'other' }], [after.url], target));
    console.log('Navigation assertion fixtures passed: valid hash plus reload; six invalid lifecycle/route cases rejected.');
    process.exit(0);
}

assert.equal(process.env.GITHUB_ACTIONS, 'true');
assert.equal(process.platform, 'linux');
assert.equal(process.env.GITHUB_RUN_ATTEMPT, '1');
const { chromium } = await import('playwright');
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
const documentStarts = [];
let original;
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
    // The init script runs once per document, never for a hash change. Keep its
    // reports outside the page so a reload loop cannot erase earlier identities.
    await page.exposeBinding('__recordPortalTestDocument', ({ frame }, document) => {
        if (frame === page.mainFrame()) documentStarts.push(document);
    });
    await page.addInitScript(() => {
        window.__portalTestDocument = { id: crypto.randomUUID(), timeOrigin: performance.timeOrigin, url: location.href };
        window.__portalTestDocumentReported = window.__recordPortalTestDocument(window.__portalTestDocument);
    });
    const documentState = () => page.evaluate(async () => {
        await window.__portalTestDocumentReported;
        return { ...window.__portalTestDocument, url: location.href,
            navigationType: performance.getEntriesByType('navigation')[0]?.type };
    });
    page.on('pageerror', error => result.pageErrors.push(error.message));
    assert.equal((await page.goto(root)).status(), 200);
    original = await inventory(page);
    result.originalRegistrations = original;
    assert.ok(!original.some(item => item.scope === target));
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller?.scriptURL ?? null), null);
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    await page.locator('a[href="portal-checker/"]').click();
    await page.waitForURL(target + '#sandbox', { waitUntil: 'load' });
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    assert.deepEqual(await inventory(page), original);
    const navigations = [];
    page.on('framenavigated', frame => { if (frame === page.mainFrame()) navigations.push(frame.url()); });
    const coldDocument = await documentState();
    const documentsBeforeActivation = documentStarts.length;
    const assertCurrentActivation = async () => {
        const current = await documentState();
        const started = documentStarts.slice(documentsBeforeActivation);
        result.activation = { coldDocument, currentDocument: current, documents: [...started], frameUrls: [...navigations] };
        assertActivation(coldDocument, current, started, navigations, target);
    };
    phase = 'activation';
    await page.locator('#portal-activate').click();
    await page.waitForFunction(previous => window.__portalTestDocument?.id !== previous, coldDocument.id);
    const baseline = await accepted();
    await assertCurrentActivation();
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
    // Keep the one-document condition in force through runtime initialization,
    // offline edits and reversion, so later automatic reloads also fail the test.
    await assertCurrentActivation();
    await page.screenshot({ path: resolve(output, 'published-portal.png'), fullPage: true });

    phase = 'cleanup';
    await context.setOffline(false);
    await Promise.all([page.waitForURL(url => url.href === root || url.href === root + '#sandbox'), page.locator('#portal-deactivate').click()]);
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
                // A new root document has no residual controller from the failed
                // portal document. Verify inventory after exact-scope removal.
                const probe = await context.newPage();
                try {
                    assert.equal((await probe.goto(root)).status(), 200);
                    const restored = await inventory(probe);
                    result.finalRegistrations = restored;
                    assert.ok(original, 'Original registration inventory was not captured.');
                    assert.deepEqual(restored, original);
                    assert.equal(await probe.evaluate(() => navigator.serviceWorker.controller?.scriptURL ?? null), null);
                    assert.equal(await probe.evaluate(() => crossOriginIsolated), false);
                    result.finalCleanupVerified = true;
                } finally { await probe.close(); }
            } catch (error) {
                result.cleanupError = error.message;
                result.passed = false;
                process.exitCode = 1;
            }
        }
        await context.tracing.stop({ path: resolve(output, 'published-portal-trace.zip') });
    }
    await writeFile(resolve(output, 'published-portal-result.json'), JSON.stringify(result, null, 2) + '\n');
    await browser?.close();
}
