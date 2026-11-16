/** Linux-only main-workspace checks against the actual compiled inclined bundle. */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { resolve } from 'node:path';

const digest = value => createHash('sha256').update(value).digest('hex');
export async function runMainInclinedCases({ page, context, output, origin, base, result }) {
    assert.equal(process.platform, 'linux');
    assert.equal(process.env.GITHUB_ACTIONS, 'true');
    const fixtureRoot = resolve('.data/live-portal/inclined-native');
    const request = JSON.parse(await readFile(resolve(fixtureRoot, 'cantilever-interior.request.json'), 'utf8'));
    const nativeReport = await readFile(resolve(fixtureRoot, 'cantilever-interior.report'), 'utf8');
    const measurements = { requests: [], cancellation: null, verified: false };
    result.mainInclined = measurements;
    await page.addInitScript(() => {
        const OriginalWorker = window.Worker;
        window.inclinedWorkerLifecycle = { created: 0, terminated: 0, framePosts: 0 };
        window.Worker = class extends OriginalWorker {
            constructor(...arguments_) { super(...arguments_); window.inclinedWorkerLifecycle.created++; }
            postMessage(...arguments_) {
                if (arguments_[0]?.protocol === 'frame') window.inclinedWorkerLifecycle.framePosts++;
                return super.postMessage(...arguments_);
            }
            terminate() { window.inclinedWorkerLifecycle.terminated++; return super.terminate(); }
        };
    });
    const importModel = model => page.locator('#model-file').setInputFiles({ name: 'synthetic-inclined.json',
        mimeType: 'application/json', buffer: Buffer.from(JSON.stringify({ version: 2, model })) });
    async function accepted() {
        await page.waitForFunction(() => {
            try { return JSON.parse(document.getElementById('portal-certificate').textContent).protocol === 'CV2011_INCLINED_1'; }
            catch { return false; }
        }, null, { timeout: 190000 });
        const receipt = JSON.parse(await page.locator('#portal-certificate').textContent());
        assert.equal(receipt.artifact, result.artifact);
        assert.equal(receipt.bundle, result.bundle);
        assert.equal(receipt.theorem, 'InclinedFrameIntervalReportSound.checkReport_sound');
        assert.equal(digest(receipt.packet), receipt.packetDigest);
        assert.equal(digest(receipt.report), receipt.reportDigest);
        assert.equal(digest(JSON.stringify(receipt.sourceRequest)), receipt.inputDigest);
        measurements.requests.push({ inputDigest: receipt.inputDigest, reportDigest: receipt.reportDigest,
            revision: receipt.revision, request: receipt.request });
        return receipt;
    }
    await page.goto(origin + base);
    await importModel(request.model);
    await page.locator('#section-member').selectOption(request.query.member);
    await page.locator('#frame-parameter').fill(String(request.query.parameter));
    await page.locator('#frame-side').selectOption(request.query.cutSide);
    await Promise.all([page.waitForNavigation(), page.locator('#frame-generate').click()]);
    const first = await accepted();
    assert.equal(first.report, nativeReport);
    await page.waitForFunction(() => document.querySelector('#frame-worked-output [data-evidence="exact-enclosure"]'));
    assert.ok(await page.locator('#frame-worked-output [data-evidence="explanatory-numerical"]').count() > 0);
    assert.equal(await page.locator('#frame-worked-output .math-error').count(), 0);
    assert.match(await page.locator('#frame-worked-output').textContent(), /do not inherit the accuracy guarantee/);
    const screenshot = resolve(output, 'main-inclined-accepted.png');
    await page.locator('#worked-panel').screenshot({ path: screenshot });
    measurements.screenshot = { file: 'main-inclined-accepted.png', sha256: digest(await readFile(screenshot)) };

    // Wait until an actual request enters the worker, then edit the section.
    // This tests termination of synchronous arithmetic, not just debounce.
    const before = await page.evaluate(() => ({ ...window.inclinedWorkerLifecycle }));
    await page.locator('#frame-parameter').fill('0.25');
    await page.waitForFunction(count => window.inclinedWorkerLifecycle.framePosts > count, before.framePosts);
    await page.locator('#frame-parameter').fill(String(request.query.parameter));
    assert.equal(await page.locator('#portal-certificate').textContent(), '');
    const afterEdit = await page.evaluate(() => ({ ...window.inclinedWorkerLifecycle }));
    assert.ok(afterEdit.terminated > before.terminated);
    const reverted = await accepted();
    assert.equal(reverted.report, nativeReport);
    assert.ok(reverted.revision > first.revision);
    const after = await page.evaluate(() => ({ ...window.inclinedWorkerLifecycle }));
    assert.ok(after.created > before.created);
    measurements.cancellation = { before, afterEdit, after };

    const changed = structuredClone(request.model);
    changed.loads[0].fy -= 1;
    await importModel(changed);
    assert.equal(await page.locator('#portal-certificate').textContent(), '');
    const mutated = await accepted();
    assert.notEqual(mutated.inputDigest, reverted.inputDigest);
    assert.notEqual(mutated.reportDigest, reverted.reportDigest);
    assert.equal(mutated.sourceRequest.model.loads[0].fy, changed.loads[0].fy);
    await page.locator('#frame-generate').click();
    const current = JSON.parse(await page.locator('#portal-certificate').textContent());
    assert.equal(current.explanation.evidence, 'explanatory-numerical');
    const download = page.waitForEvent('download');
    await page.locator('#frame-export').evaluate(element => { element.closest('details').open = true; });
    await page.locator('#frame-export').click();
    assert.deepEqual(JSON.parse(await readFile(await (await download).path(), 'utf8')), current);
    await Promise.all([page.waitForNavigation(), page.locator('#portal-deactivate').click()]);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller), null);
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    measurements.verified = true;
    result.cases.push('main-inclined-native-report-rendering-cancellation-mutation-export-cleanup');
}
