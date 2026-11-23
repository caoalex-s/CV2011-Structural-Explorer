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
        // Diagram and displacement workers also use the frame protocol. Observe
        // only the compiled equilibrium worker that serves this fixture.
        const lifecycle = { workers: [], posts: [], replies: [], terminated: [], edit: null };
        window.inclinedWorkerLifecycle = lifecycle;
        window.Worker = class extends OriginalWorker {
            constructor(url, options) {
                super(url, options);
                if (!new URL(url, location.href).pathname.endsWith('/bundle/worker.mjs')) return;
                this.testWorkerId = lifecycle.workers.push(String(url));
                this.addEventListener('message', ({data}) => {
                    if (data.state === 'accepted') lifecycle.replies.push({
                        worker: this.testWorkerId, request: data.id, digest: data.inputDigest
                    });
                });
            }
            postMessage(...args) {
                const sent = super.postMessage(...args);
                const message = args[0];
                if (!this.testWorkerId || !message?.intervalProposal || message.protocol !== 'frame') return sent;
                const {query} = JSON.parse(new TextDecoder().decode(message.bytes));
                const post = {worker:this.testWorkerId, request:message.id, member:query.member, parameter:query.parameter};
                lifecycle.posts.push(post);
                const edit = window.editAfterInclinedPost;
                if (edit && post.member === edit.member && post.parameter === edit.parameter) {
                    window.editAfterInclinedPost = null;
                    // The original post is already dispatched. Run the real input
                    // handler before a worker reply can be delivered on a later task.
                    queueMicrotask(() => {
                        const parameter = document.querySelector('#frame-parameter');
                        parameter.value = String(edit.restore);
                        parameter.dispatchEvent(new Event('input', {bubbles:true}));
                        lifecycle.edit = {...post, cleared:document.querySelector('#portal-certificate').textContent === ''};
                    });
                }
                return sent;
            }
            terminate() {
                if (this.testWorkerId) lifecycle.terminated.push(this.testWorkerId);
                return super.terminate();
            }
        };
    });
    async function importModel(model) {
        await page.locator('#model-file').setInputFiles({ name: 'synthetic-inclined.json',
            mimeType: 'application/json', buffer: Buffer.from(JSON.stringify({ version: 2, model })) });
        // Both drawings contain AB. Verify the active coordinates and load before Generate.
        await page.waitForFunction(expected => {
            const active = JSON.parse(localStorage.getItem('cv2011-model') || 'null');
            return !document.getElementById('workspace').inert && active &&
                JSON.stringify(active.nodes) === JSON.stringify(expected.nodes) &&
                active.loads[0].fy === expected.loads[0].fy;
        }, model);
    }
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
    assert.deepEqual(first.sourceRequest.model.nodes, request.model.nodes);
    assert.equal(first.report, nativeReport);
    await page.waitForFunction(() => document.querySelector('#frame-worked-output [data-evidence="exact-enclosure"]'));
    const exact = value => value.denominator === '1' ? value.numerator : `${value.numerator}/${value.denominator}`;
    const allValues = [...first.values.fields, ...first.values.points.flatMap(point => point.reactions)];
    assert.deepEqual(await page.locator('#frame-worked-output [data-evidence="exact-midpoint"]').allTextContents(),
        allValues.map(value => exact(value.midpoint)));
    assert.deepEqual(await page.locator('#frame-worked-output [data-evidence="exact-enclosure"]').allTextContents(),
        allValues.map(value => `[${exact(value.lower)}, ${exact(value.upper)}]`));
    const outward = await page.locator('#frame-worked-output [data-evidence="outward-enclosure"]').allTextContents();
    assert.equal(outward.length, allValues.length);
    for (const [index, text] of outward.entries()) {
        const match = /^\[(-?\d+\.\d+), (-?\d+\.\d+)\]$/.exec(text);
        assert.ok(match);
        const fraction = decimal => ({ numerator: BigInt(decimal.replace('.', '')),
            denominator: 10n ** BigInt(decimal.split('.')[1].length) });
        const lower = fraction(match[1]), upper = fraction(match[2]);
        assert.ok(lower.numerator * BigInt(allValues[index].lower.denominator) <=
            BigInt(allValues[index].lower.numerator) * lower.denominator);
        assert.ok(upper.numerator * BigInt(allValues[index].upper.denominator) >=
            BigInt(allValues[index].upper.numerator) * upper.denominator);
    }
    assert.ok(await page.locator('#frame-worked-output [data-evidence="explanatory-numerical"]').count() > 0);
    assert.equal(await page.locator('#frame-worked-output .math-error').count(), 0);
    assert.match(await page.locator('#frame-worked-output').textContent(), /do not inherit the accuracy guarantee/);
    const screenshot = resolve(output, 'main-inclined-accepted.png');
    await page.locator('#worked-panel').screenshot({ path: screenshot });
    measurements.screenshot = { file: 'main-inclined-accepted.png', sha256: digest(await readFile(screenshot)) };

    await page.evaluate(settings => { window.editAfterInclinedPost = settings; }, {
        member: request.query.member, parameter: 0.25, restore: request.query.parameter
    });
    await page.locator('#frame-parameter').fill('0.25');
    await page.waitForFunction(() => window.inclinedWorkerLifecycle.edit !== null);
    const reverted = await accepted();
    assert.equal(reverted.report, nativeReport);
    assert.ok(reverted.revision > first.revision);
    const lifecycle = await page.evaluate(() => window.inclinedWorkerLifecycle);
    const interrupted = lifecycle.edit;
    assert.equal(interrupted.cleared, true);
    assert.ok(lifecycle.terminated.includes(interrupted.worker));
    assert.ok(!lifecycle.replies.some(reply => reply.worker === interrupted.worker && reply.request === interrupted.request));
    const replacement = lifecycle.replies.find(reply => reply.worker > interrupted.worker &&
        reply.request === reverted.request && reply.digest === reverted.inputDigest);
    assert.ok(replacement, 'A newly created equilibrium worker must return the accepted receipt');
    assert.ok(lifecycle.posts.some(post => post.worker === replacement.worker &&
        post.request === replacement.request && post.member === request.query.member && post.parameter === request.query.parameter));
    measurements.cancellation = lifecycle;

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
