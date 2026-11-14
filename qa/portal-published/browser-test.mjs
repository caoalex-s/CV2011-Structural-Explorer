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
assert.equal(binding.deployed_main, '689a0353199f1ac8cbd2fcdd5bf23718fecc24d7');
const root = 'https://caoalex-s.github.io/CV2011-Structural-Explorer/';
const target = root;
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
async function accepted(kind = 'solution', generate = true) {
    if (generate) await page.locator('#worked-panel #frame-generate').click();
    await page.waitForFunction(() => {
        try { return !!JSON.parse(document.getElementById('portal-certificate').textContent).workedSolution; }
        catch { return false; }
    });
    const certificate = JSON.parse(await page.locator('#portal-certificate').textContent());
    assert.equal(certificate.values.kind, kind);
    const worked = certificate.workedSolution;
    // The source schema fills omitted rigid-joint/restraint defaults. Compare
    // its exact parsed model, preserving source order and all display labels.
    const parsedSource = await page.evaluate(async source =>
        (await import('./model-evidence.js')).parseEvidenceModel(source), certificate.sourceRequest.model);
    assert.deepEqual(worked.model, parsedSource);
    assert.deepEqual(worked.query, certificate.sourceRequest.query);
    assert.deepEqual(worked.values, certificate.values);
    for (const key of ['revision', 'request', 'bindings', 'artifact', 'bundle', 'inputDigest', 'packetDigest'])
        assert.deepEqual(worked.binding[key], certificate[key]);
    assert.ok(worked.steps.every(step => step.evidence === 'explanatory-rule'));
    const fields = ['N', 'V', 'M', 'rotation', 'ux', 'uy'];
    for (const step of worked.steps.filter(step => step.result)) {
        assert.equal(step.result.evidence, 'verified-result');
        assert.deepEqual(step.result.value, certificate.values.readouts[fields.indexOf(step.id)]);
    }
    assert.equal(await page.locator('#frame-worked-output .math-error').count(), 0);
    assert.match(await page.locator('#frame-worked-output').textContent(), /not separately Lean-checked/);
    assert.match(await page.locator('#frame-overview-convention').textContent(), /Numerical overview:.*right-hand convention/);
    assert.match(await page.locator('#portal-status').textContent(), new RegExp(`Checked section: ${worked.query.cutSide} limit`));
    assert.equal(certificate.artifact, binding.wasm_sha256);
    assert.equal(certificate.bundle, binding.manifest_sha256);
    assert.equal(certificate.theorem, 'RationalFrameSoundness.acceptance_actual_frame');
    return certificate;
}
async function importModel(model) {
    await page.locator('#model-file').setInputFiles({ name: 'public-frame.json', mimeType: 'application/json',
        buffer: Buffer.from(JSON.stringify({ version: 2, model })) });
    await page.waitForFunction(expected => {
        const saved = JSON.parse(localStorage.getItem('cv2011-model'));
        const withoutLabels = value => ({ ...value, loads: value.loads.map(({ label, ...load }) => load) });
        return saved && JSON.stringify(withoutLabels(saved)) === JSON.stringify(withoutLabels(expected));
    }, model);
}
async function select(member, parameter = '0.5', side = 'left') {
    await page.locator('#section-member').selectOption(member);
    await page.locator('#frame-parameter').fill(parameter);
    await page.locator('#frame-side').selectOption(side);
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
    const publicModel = await page.evaluate(async () => {
        const model = (await import('./engine.js')).example('frame');
        model.loads[0].fy = -5; model.loads[0].qEnd = 5;
        model.loads[0].label = 'w_1';
        return model;
    });
    await importModel(publicModel);
    await select('BC', '0.25', 'left');
    await page.waitForURL(target + '#sandbox');
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
    await page.locator('#worked-panel #frame-generate').click();
    await page.waitForFunction(previous => window.__portalTestDocument?.id !== previous, coldDocument.id);
    const baseline = await accepted('solution', false);
    await assertCurrentActivation();
    assert.equal(await page.evaluate(() => crossOriginIsolated), true);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller.scriptURL), target + 'main-checker-sw.js');
    assert.deepEqual((await inventory(page)).filter(item => item.scope !== target), original);
    assert.equal(baseline.sourceRequest.model.loads[0].fy, -5);
    assert.equal(baseline.sourceRequest.model.loads[0].qEnd, 5);
    assert.deepEqual(baseline.sourceRequest.model.nodes, publicModel.nodes);
    const expectedModel = await page.evaluate(async model =>
        (await import('./model-evidence.js')).parseEvidenceModel(model), publicModel);
    assert.deepEqual(baseline.workedSolution.model, expectedModel);
    assert.equal(baseline.sourceRequest.query.member, 'BC');
    assert.equal(baseline.sourceRequest.query.parameter, 0.25);
    assert.equal(baseline.sourceRequest.query.cutSide, 'left');
    const number = value => Number(value.numerator) / Number(value.denominator);
    const leftReaction = number(baseline.values.points.find(point => point.id === 'A').reaction[1]);
    const rightReaction = number(baseline.values.points.find(point => point.id === 'D').reaction[1]);
    assert.ok(leftReaction > 0 && rightReaction < 0);
    assert.equal(leftReaction + rightReaction, 0);
    result.baseline = baseline;

    result.browserAssetHashes = await page.evaluate(async names => {
        const values = {};
        for (const name of names) {
            const bytes = await (await fetch('./portal-checker/bundle/' + name)).arrayBuffer();
            values[name] = [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))]
                .map(byte => byte.toString(16).padStart(2, '0')).join('');
        }
        return values;
    }, ['manifest.json', 'worker.mjs', 'checker.wasm', 'checker.mjs', 'checker.worker.js', 'checker.mjs.symbols',
        'frame-rational.js', 'model-evidence.js', 'frame-candidate.js', 'frame-packet.js', 'frame-result.js']);
    for (const [name, actual] of Object.entries(result.browserAssetHashes)) {
        assert.equal(actual, binding.artifact_file_hashes['portal-checker/bundle/' + name]);
    }
    const neighbor = await context.newPage();
    assert.equal((await neighbor.goto(root + 'learn/')).status(), 200);
    assert.equal(await neighbor.evaluate(() => navigator.serviceWorker.controller?.scriptURL ?? null), root + 'main-checker-sw.js');
    assert.equal(await neighbor.evaluate(() => crossOriginIsolated), false);
    await neighbor.close();

    phase = 'offline';
    await context.setOffline(true);
    await page.locator('[data-object="load"][data-id="q1"] > path[stroke][fill="none"]').click();
    await page.locator('[data-property="qEnd"]').fill('-6');
    await page.locator('[data-property="qEnd"]').press('Tab');
    assert.equal(await page.locator('#frame-worked-output').textContent(), '');
    const edited = await accepted();
    assert.equal(edited.sourceRequest.model.loads[0].qEnd, 6);
    assert.ok(edited.request > baseline.request && edited.revision > baseline.revision);
    assert.notEqual(edited.inputDigest, baseline.inputDigest);
    result.edited = edited;
    await page.locator('#undo').click();
    const restored = await accepted();
    assert.equal(restored.sourceRequest.model.loads[0].qEnd, 5);
    assert.ok(restored.request > edited.request && restored.revision > edited.revision);
    assert.deepEqual(restored.values.readouts, baseline.values.readouts);
    result.restored = restored;
    await page.locator('#frame-export').evaluate(element => { element.closest('details').open = true; });
    const downloading = page.waitForEvent('download');
    await page.locator('#frame-export').click();
    assert.deepEqual(JSON.parse(await readFile(await (await downloading).path(), 'utf8')), restored);
    result.offlineHttpRequests = result.requests.filter(item => item.phase === 'offline' && /^https?:/.test(item.url));
    assert.deepEqual(result.offlineHttpRequests, []);
    assert.ok(result.requests.every(item => item.method === 'GET'));
    await assertCurrentActivation();
    await page.screenshot({ path: resolve(output, 'published-main-affine.png'), fullPage: true });

    phase = 'cleanup';
    await context.setOffline(false);
    const beforeDisable = await documentState();
    await Promise.all([page.waitForNavigation({ waitUntil: 'load' }), page.locator('#portal-deactivate').click()]);
    const afterDisable = await documentState();
    assert.equal(afterDisable.url, beforeDisable.url);
    assert.notEqual(afterDisable.id, beforeDisable.id);
    assert.ok(afterDisable.timeOrigin > beforeDisable.timeOrigin);
    assert.equal(afterDisable.navigationType, 'reload');
    result.deactivation = { beforeDisable, afterDisable };
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
                    const exact = (await navigator.serviceWorker.getRegistrations()).find(item => item.scope === scope &&
                        [item.active, item.waiting, item.installing].some(worker => worker?.scriptURL === scope + 'main-checker-sw.js'));
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
