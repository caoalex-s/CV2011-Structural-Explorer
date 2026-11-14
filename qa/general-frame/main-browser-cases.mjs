/** Main-workspace lifecycle with a public synthetic sign-changing portal.
 * Linux CI only. The original screenshot supplies no dimensions or model file.
 */
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';

export async function runMainCases({ page, context, output, origin, base, result, setOffline }) {
    assert.equal(process.platform, 'linux');
    assert.equal(process.env.GITHUB_ACTIONS, 'true');
    const main = origin + base, portal = main + 'portal-checker/';
    const ownScript = main + 'main-checker-sw.js', sentinel = main + 'neighbor/';
    const number = value => Number(value.numerator) / Number(value.denominator);
    const inventory = () => page.evaluate(async () => (await navigator.serviceWorker.getRegistrations())
        .map(r => ({ scope: r.scope, script: r.active?.scriptURL })).sort((a, b) => a.scope.localeCompare(b.scope)));
    async function currentReport() {
        await page.waitForFunction(() => {
            try { return !!JSON.parse(document.getElementById('portal-certificate').textContent).workedSolution; }
            catch { return false; }
        });
        const receipt = JSON.parse(await page.locator('#portal-certificate').textContent());
        assert.equal(receipt.theorem, 'RationalFrameSoundness.acceptance_actual_frame');
        assert.equal(receipt.artifact, result.artifact);
        assert.equal(receipt.bundle, result.bundle);
        const normalized = await page.evaluate(async source => {
            const { parseEvidenceModel } = await import('./model-evidence.js');
            return parseEvidenceModel(source);
        }, receipt.sourceRequest.model);
        assert.deepEqual(receipt.workedSolution.model, normalized);
        assert.deepEqual(receipt.workedSolution.query, receipt.sourceRequest.query);
        for (const key of ['revision', 'request', 'inputDigest', 'packetDigest', 'artifact', 'bundle'])
            assert.equal(receipt.workedSolution.binding[key], receipt[key]);
        assert.deepEqual(receipt.workedSolution.binding.bindings, receipt.bindings);
        assert.deepEqual(receipt.workedSolution.values, receipt.values);
        assert.ok(receipt.workedSolution.steps.every(step => step.evidence === 'explanatory-rule'));
        assert.deepEqual(receipt.workedSolution.steps.filter(step => step.result).map(step => step.result.value), receipt.values.readouts);
        assert.ok(receipt.workedSolution.steps.filter(step => step.result).every(step => step.result.evidence === 'verified-result'));
        assert.equal(await page.locator('#frame-worked-output .math-error').count(), 0);
        return receipt;
    }
    async function generate() {
        await page.locator('#frame-generate').click();
        return currentReport();
    }
    await page.goto(main);
    await page.locator('#frame-generate').waitFor();
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    const originalInventory = await inventory();
    // A foreign owner at this exact scope must never be replaced by Generate.
    await page.evaluate(async root => {
        const registration = await navigator.serviceWorker.register(root + 'foreign-checker-fixture.js', { scope: root });
        await new Promise(resolve => {
            const timer = setInterval(() => { if (registration.active) { clearInterval(timer); resolve(); } }, 20);
        });
    }, main);
    await page.reload();
    await page.locator('#frame-generate').click();
    await page.waitForFunction(() => document.getElementById('portal-status').textContent.includes('Another service worker owns this scope'));
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller.scriptURL), main + 'foreign-checker-fixture.js');
    assert.equal(await page.locator('#portal-certificate').textContent(), '');
    await page.evaluate(async root => {
        for (const registration of await navigator.serviceWorker.getRegistrations())
            if (registration.scope === root && registration.active?.scriptURL === root + 'foreign-checker-fixture.js') await registration.unregister();
    }, main);
    await page.reload();
    result.cases.push('main-foreign-root-registration-refused-without-replacement');
    await page.evaluate(async scope => {
        const registration = await navigator.serviceWorker.register(scope + 'sentinel-sw.js', { scope });
        await new Promise(resolve => {
            const timer = setInterval(() => { if (registration.active) { clearInterval(timer); resolve(); } }, 20);
        });
        await caches.open('main-affine-unrelated-fixture');
    }, sentinel);
    const beforeInventory = await inventory();
    const publicModel = await page.evaluate(async () => {
        const { example } = await import('./engine.js');
        const model = example('frame'); model.loads[0].fy = -5; model.loads[0].qEnd = 5;
        return model;
    });
    await page.locator('#model-file').setInputFiles({ name: 'synthetic-affine-portal.json', mimeType: 'application/json',
        buffer: Buffer.from(JSON.stringify({ version: 2, model: publicModel })) });
    await page.locator('#section-member').selectOption('BC');
    await page.locator('#frame-parameter').fill('0.25');
    await page.locator('#frame-side').selectOption('left');
    await page.locator('#moment-side').selectOption('compression');
    await page.locator('[data-object="node"][data-id="C"]').click();
    assert.match(await page.locator('#inspector').textContent(), /Node properties/);
    assert.equal(await page.locator('[data-property="x"]').inputValue(), '6');
    await page.locator('#zoom-in').click();
    await page.locator('#focus-workspace').click();
    const savedModel = await page.evaluate(() => JSON.parse(localStorage.getItem('cv2011-model')));
    const undoEnabled = await page.locator('#undo').isEnabled();
    const beforeDocument = await page.evaluate(() => {
        window.mainActivationIdentity = 'before-activation';
        return performance.timeOrigin;
    });
    const activationUrl = page.url();
    let navigations = 0;
    const navigation = frame => { if (frame === page.mainFrame()) navigations++; };
    page.on('framenavigated', navigation);
    await Promise.all([page.waitForNavigation(), page.locator('#frame-generate').click()]);
    // Automatic post-activation Generate must succeed without a second click.
    const first = await currentReport();
    assert.equal(page.url(), activationUrl);
    assert.equal(navigations, 1);
    assert.equal(await page.evaluate(() => window.mainActivationIdentity), undefined);
    assert.notEqual(await page.evaluate(() => performance.timeOrigin), beforeDocument);
    assert.equal(await page.evaluate(() => performance.getEntriesByType('navigation')[0].type), 'reload');
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller.scriptURL), ownScript);
    assert.equal(await page.evaluate(() => crossOriginIsolated), true);
    assert.deepEqual(await page.evaluate(() => JSON.parse(localStorage.getItem('cv2011-model'))), savedModel);
    assert.equal(await page.locator('#frame-parameter').inputValue(), '0.25');
    assert.equal(await page.locator('#frame-side').inputValue(), 'left');
    assert.equal(await page.locator('#moment-side').inputValue(), 'compression');
    assert.equal(await page.locator('#focus-workspace').getAttribute('aria-pressed'), 'true');
    assert.equal(await page.locator('#undo').isEnabled(), undoEnabled);
    assert.match(await page.locator('#inspector').textContent(), /Node properties/);
    assert.equal(await page.locator('[data-property="x"]').inputValue(), '6');
    assert.equal(await page.locator('[data-property="y"]').inputValue(), '4');
    assert.equal(first.values.query.member, 'BC');
    assert.equal(number(first.values.query.parameter), 0.25);
    const leftReaction = first.values.points.find(point => point.id === 'A').reaction;
    const rightReaction = first.values.points.find(point => point.id === 'D').reaction;
    assert.ok(number(leftReaction[1]) > 0 && number(rightReaction[1]) < 0);
    assert.equal(number(leftReaction[1]) + number(rightReaction[1]), 0);
    assert.match(await page.locator('#frame-worked-output').textContent(), /drawing w = 5 to -5/);
    // Arrows carry the reaction sign; canvas labels show magnitudes.
    const arrows = await page.locator('#canvas g[pointer-events="none"] [data-vector="force"]').evaluateAll(elements =>
        elements.map(element => ({ label: element.textContent, shaft: element.querySelector('path.hit').getAttribute('d') })));
    const shaftDirection = label => {
        const arrow = arrows.find(arrow => arrow.label.includes(label));
        assert.ok(arrow, label);
        const numbers = arrow.shaft.match(/-?\d+(?:\.\d+)?(?:e[+-]?\d+)?/gi).map(Number);
        return numbers[3] - numbers[1];
    };
    assert.ok(shaftDirection('A') < 0 && shaftDirection('D') > 0);
    result.cases.push('main-cold-generate-same-url-single-reload-state-history-affine-signed-reactions');
    await page.screenshot({ path: resolve(output, 'main-affine-accepted.png'), fullPage: true });

    const learn = await context.newPage();
    const response = await learn.goto(main + 'learn/beam-basics/');
    assert.equal(response.headers()['cross-origin-embedder-policy'], undefined);
    assert.equal(await learn.evaluate(() => crossOriginIsolated), false);
    assert.equal(await learn.evaluate(() => navigator.serviceWorker.controller.scriptURL), ownScript);
    await learn.close();
    assert.ok(await page.evaluate(async () => (await caches.keys()).includes('main-affine-unrelated-fixture')));
    result.cases.push('learn-root-controlled-but-unisolated-pass-through-and-unrelated-cache-preserved');

    await setOffline(true);
    const offlineStart = result.offlineRequests.length;
    await page.locator('#focus-workspace').click();
    await page.locator('#close-inspector').click();
    // Click the visible envelope, which shares the load's normal selection
    // handler. Its painted stroke sits above the wider transparent hit path.
    const loadEnvelope = page.locator('[data-object="load"][data-id="q1"] > path[stroke][fill="none"]');
    assert.equal(await loadEnvelope.count(), 1);
    await loadEnvelope.click();
    assert.equal(await page.locator('[data-property="qEnd"]').inputValue(), '-5');
    await page.evaluate(() => {
        window.mainEndpointChanges = [];
        document.addEventListener('change', event => {
            if (event.target.matches('[data-property="qEnd"]'))
                window.mainEndpointChanges.push({ value: event.target.value, trusted: event.isTrusted });
        }, true);
    });
    const storedEndpoint = () => page.evaluate(() => JSON.parse(localStorage.getItem('cv2011-model')).loads[0].qEnd);
    const editEndpoint = async value => {
        await page.locator('[data-property="qEnd"]').fill(value);
        // Let the browser commit the focused field once, as a user does. A
        // synthetic change leaves the field's native edit lifecycle unfinished.
        await page.locator('[data-property="qEnd"]').press('Tab');
        assert.equal(await storedEndpoint(), -Number(value));
        assert.equal(await page.locator('#frame-worked-output').textContent(), '');
        return generate();
    };
    const editedLoad = await editEndpoint('-6');
    assert.equal(editedLoad.sourceRequest.model.loads[0].qEnd, 6);
    assert.notEqual(editedLoad.inputDigest, first.inputDigest);
    const restoredLoad = await editEndpoint('-5');
    assert.equal(restoredLoad.sourceRequest.model.loads[0].qEnd, 5);
    assert.ok(restoredLoad.request > editedLoad.request);
    // Re-entering the current value must not add a drawing to undo history.
    await page.locator('[data-property="qEnd"]').fill('-5');
    await page.locator('[data-property="qEnd"]').press('Tab');
    result.mainEndpointChanges = await page.evaluate(() => window.mainEndpointChanges);
    assert.deepEqual(result.mainEndpointChanges, [{ value: '-6', trusted: true }, { value: '-5', trusted: true }]);
    await page.locator('#undo').click();
    assert.equal(await storedEndpoint(), 6);
    assert.equal(await page.locator('#frame-worked-output').textContent(), '');
    assert.equal((await generate()).sourceRequest.model.loads[0].qEnd, 6);
    await page.locator('#undo').click();
    assert.equal(await storedEndpoint(), 5);
    assert.equal((await generate()).sourceRequest.model.loads[0].qEnd, 5);
    await page.locator('#redo').click();
    assert.equal(await storedEndpoint(), 6);
    assert.equal((await generate()).sourceRequest.model.loads[0].qEnd, 6);
    await page.locator('#redo').click();
    assert.equal(await storedEndpoint(), 5);
    assert.equal((await generate()).sourceRequest.model.loads[0].qEnd, 5);
    assert.equal(await page.locator('#redo').isEnabled(), false);
    result.cases.push('main-affine-endpoint-inspector-edit-revert-undo-redo-current-binding');
    for (const parameter of ['0.5', '0.75', '0.25']) {
        await page.locator('#frame-parameter').fill(parameter);
        assert.equal(await page.locator('#frame-worked-output').textContent(), '');
        await page.locator('#frame-generate').click();
    }
    const reverted = await currentReport();
    assert.ok(reverted.request > first.request && reverted.revision > first.revision);
    await page.locator('#frame-parameter').fill('');
    assert.equal(await page.locator('#portal-certificate').textContent(), '');
    await page.locator('#frame-parameter').fill('0.25');
    const latest = await generate();
    assert.ok(latest.request > reverted.request);
    const download = page.waitForEvent('download');
    await page.locator('#frame-export').evaluate(element => { element.closest('details').open = true; });
    await page.locator('#frame-export').click();
    assert.deepEqual(JSON.parse(await readFile(await (await download).path(), 'utf8')), latest);
    assert.deepEqual(result.offlineRequests.slice(offlineStart).filter(url => /^https?:/.test(url)), []);
    assert.equal(navigations, 1);
    page.off('framenavigated', navigation);
    await setOffline(false);
    result.cases.push('main-offline-affine-query-revert-blank-restore-fresh-export');

    // A more-specific existing checker remains independently owned.
    const scoped = await context.newPage();
    await scoped.goto(portal);
    await scoped.locator('#frame-generate').waitFor();
    await Promise.all([scoped.waitForNavigation(), scoped.locator('#frame-generate').click()]);
    await scoped.waitForFunction(() => document.getElementById('portal-certificate').textContent.includes('workedSolution'));
    assert.equal(await scoped.evaluate(() => navigator.serviceWorker.controller.scriptURL), portal + 'isolation-sw.js');
    await scoped.locator('#portal-deactivate').click();
    await scoped.waitForURL(url => url.origin + url.pathname === main);
    await scoped.close();
    assert.ok((await inventory()).some(item => item.script === ownScript));
    result.cases.push('root-and-scoped-checker-independent-activation-and-cleanup');

    await Promise.all([page.waitForNavigation(), page.locator('#portal-deactivate').click()]);
    assert.equal(page.url(), activationUrl);
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller), null);
    assert.deepEqual(await inventory(), beforeInventory);
    assert.ok(await page.evaluate(async () => (await caches.keys()).includes('main-affine-unrelated-fixture')));
    assert.deepEqual(await page.evaluate(() => JSON.parse(localStorage.getItem('cv2011-model'))), savedModel);
    await page.evaluate(async scope => {
        for (const registration of await navigator.serviceWorker.getRegistrations())
            if (registration.scope === scope && registration.active?.scriptURL === scope + 'sentinel-sw.js') await registration.unregister();
        await caches.delete('main-affine-unrelated-fixture');
    }, sentinel);
    assert.deepEqual(await inventory(), originalInventory);
    result.mainCleanupVerified = true;
    result.cases.push('main-own-only-disable-same-url-model-preserved-registration-inventory-restored');
}
