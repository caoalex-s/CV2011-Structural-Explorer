/** Actual compiled generic checker cases in the existing isolated workspace.
 * Invoked by the accepted portal browser harness, never executed locally.
 */
import assert from 'node:assert/strict';
import { readFile, readdir } from 'node:fs/promises';
import { resolve } from 'node:path';

export async function runFrameCases({ page, context, output, origin, base, url, result, setOffline }) {
    assert.equal(process.platform, 'linux');
    assert.equal(process.env.GITHUB_ACTIONS, 'true');
    const support = (id, member, t, kind = 'roller') => ({ id, member, t, kind, angle: 90 });
    const load = (id, member, t = 0, end = 1, fy = -5) =>
        ({ id, member, kind: 'distributed', t, end, fx: 0, fy, mz: 0, qEnd: fy });
    const beam = {
        nodes: [{ id: 'left', x: 0, y: 0 }, { id: 'right', x: 8, y: 0 }],
        members: [{ id: 'beam', a: 'left', b: 'right', EA: 2000000, EI: 20000 }],
        supports: [support('a', 'beam', 0, 'pin'), support('b', 'beam', 0.5), support('c', 'beam', 1)],
        loads: [load('w', 'beam')],
    };
    const number = value => Number(value.numerator) / Number(value.denominator);
    async function accepted(kind = 'solution') {
        await page.waitForFunction(expected => {
            try { return JSON.parse(document.getElementById('portal-certificate').textContent).values.kind === expected; }
            catch { return false; }
        }, kind);
        return JSON.parse(await page.locator('#portal-certificate').textContent());
    }
    async function select(member, parameter = 0.5, side = 'left') {
        await page.locator('#section-member').selectOption(member);
        await page.locator('#section-position').evaluate((element, value) => { element.value = String(value * 1000); }, parameter);
        await page.locator('#section-position').dispatchEvent('input');
        await page.locator('#frame-side').selectOption(side);
    }
    async function importModel(model) {
        await page.locator('#model-file').setInputFiles({ name: 'public-frame.json', mimeType: 'application/json',
            buffer: Buffer.from(JSON.stringify({ version: 2, model })) });
        await page.waitForFunction(expected => {
            const saved = JSON.parse(localStorage.getItem('cv2011-checked-portal-model/v1'));
            const withoutLabels = value => ({ ...value, loads: value.loads.map(({ label, ...load }) => load) });
            return saved && JSON.stringify(withoutLabels(saved)) === JSON.stringify(withoutLabels(expected));
        }, model);
    }
    async function check(model, member, parameter = 0.5, side = 'left', kind = 'solution') {
        await importModel(model);
        await select(member, parameter, side);
        return accepted(kind);
    }
    async function editProperty(type, id, property, value) {
        const object = page.locator(`[data-object="${type}"][data-id="${id}"]`);
        if (type === 'member') {
            // A horizontal SVG path has a zero-height geometric box despite
            // its visible stroke. Click its screen midpoint with real input.
            const midpoint = await object.locator('path').first().evaluate(path => {
                const point = path.getPointAtLength(path.getTotalLength() / 2);
                const screen = new DOMPoint(point.x, point.y).matrixTransform(path.getScreenCTM());
                return { x: screen.x, y: screen.y };
            });
            await page.mouse.click(midpoint.x, midpoint.y);
        } else await object.click();
        const input = page.locator(`[data-property="${property}"]`);
        await input.fill(String(value));
        await input.dispatchEvent('change');
    }

    const rootResponse = await page.goto(origin + base);
    assert.equal(rootResponse.status(), 200);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller), null);
    const sentinelScope = origin + base + 'neighbor/';
    await page.evaluate(async scope => navigator.serviceWorker.register(scope + 'sentinel-sw.js', { scope }), sentinelScope);
    await page.locator('a[href="portal-checker/"]').click();
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    // The slider exists in the static HTML before app.ts binds its input
    // handler. The generated panel appears only after those bindings exist.
    await page.locator('#portal-activate').waitFor({ state: 'visible' });
    await page.locator('#section-position').evaluate(element => { element.value = '400'; });
    await page.locator('#section-position').dispatchEvent('input');
    assert.equal(await page.locator('#section-position').inputValue(), '400');
    await Promise.all([page.waitForNavigation(), page.locator('#portal-activate').click()]);
    assert.equal(await page.locator('#section-position').inputValue(), '400');
    const first = await accepted();
    assert.equal(await page.evaluate(() => crossOriginIsolated), true);
    assert.equal(first.values.query.member, 'BC');
    assert.equal(number(first.values.query.parameter), 0.4);
    const originalPortal = first.sourceRequest.model;
    await select('BC');
    const originalResponse = await accepted();
    assert.match(await page.locator('#portal-readouts').textContent(), /11\.262/);
    assert.match(await page.locator('#portal-readouts').textContent(), /-1\.720/);
    result.cases.push('generic-activation-restores-query-and-original-portal');

    // The direct test instance exercises the same actual artifact. The UI
    // continues to use its single bounded production worker throughout.
    await page.evaluate(async () => {
        const { default: createChecker } = await import('./bundle/checker.mjs');
        window.abiFixture = await createChecker();
        if (window.abiFixture._checker_init() !== 1) throw Error('Fixture initialization');
        window.portalFixture = await import('./portal-candidate.js');
        window.runtimeFixture = await import('./portal-runtime.js');
    });
    const packets = [];
    for (const name of (await readdir('.data/general-frame-packets')).filter(name => name.endsWith('.packet')).sort()) {
        packets.push({ name, text: await readFile(resolve('.data/general-frame-packets', name), 'utf8') });
    }
    const abi = await page.evaluate(fixtures => {
        const module = window.abiFixture, pointer = module._input_ptr();
        const run = bytes => { module.HEAPU8.set(bytes, pointer); return module._checker_check(pointer, bytes.length); };
        const results = fixtures.map(({ name, text }) => {
            const start = performance.now(), code = run(new TextEncoder().encode(text));
            return { name, code, milliseconds: performance.now() - start };
        });
        const portal = run(window.portalFixture.encodeCandidate(window.portalFixture.portalCandidate(-5)));
        return { results, portal, pointer: module._checker_check(pointer + 1, 1),
            oversized: module._checker_check(pointer, module._input_capacity() + 1) };
    }, packets);
    for (const entry of abi.results) assert.equal(entry.code, Number(entry.name[0]), entry.name);
    assert.equal(abi.portal, 1); assert.equal(abi.pointer, 2); assert.equal(abi.oversized, 3);
    result.abi = abi;
    result.cases.push('actual-wasm-generic-packets-and-fixed-portal-abi');

    const neighbor = await context.newPage();
    await neighbor.goto(origin + base);
    assert.equal(await neighbor.evaluate(() => navigator.serviceWorker.controller), null);
    await neighbor.close();
    await setOffline(true);
    const single = await check(beam, 'beam');
    assert.equal(single.artifact, first.artifact);
    assert.equal(number(single.values.readouts[2]), -10);
    assert.deepEqual(single.values.points.map(point => number(point.reaction[1])), [7.5, 7.5, 25]);
    const joined = {
        nodes: [beam.nodes[0], { id: 'middle', x: 4, y: 0 }, beam.nodes[1]],
        members: [{ ...beam.members[0], id: 'first', b: 'middle' }, { ...beam.members[0], id: 'second', a: 'middle' }],
        supports: [support('a', 'first', 0, 'pin'), support('b', 'first', 1), support('c', 'second', 1)],
        loads: [load('w1', 'first'), load('w2', 'second')],
    };
    const two = await check(joined, 'first', 1);
    assert.deepEqual(two.values.points.map(point => number(point.reaction[1])), [7.5, 25, 7.5]);
    assert.equal(number(two.values.readouts[2]), -10);
    result.cases.push('offline-one-and-two-original-member-continuous-beams');

    // Exercise the ordinary inspector as well as file import. Every edit
    // must reach a fresh certificate from the same installed artifact.
    await editProperty('node', 'right', 'x', 10);
    assert.equal((await accepted()).sourceRequest.model.nodes[2].x, 10);
    await editProperty('member', 'second', 'EI', 30000);
    assert.equal((await accepted()).sourceRequest.model.members[1].EI, 30000);
    await editProperty('support', 'b', 't', 0.75);
    assert.equal((await accepted()).sourceRequest.model.supports[1].t, 0.75);
    await editProperty('load', 'w2', 't', 0.25);
    assert.equal((await accepted()).sourceRequest.model.loads[1].t, 0.25);
    result.cases.push('offline-inspector-dimension-material-support-and-load-edits');

    const shortBeam = structuredClone(beam);
    shortBeam.nodes[1].x = 1 / 128;
    const shortResponse = await check(shortBeam, 'beam');
    assert.equal(shortResponse.sourceRequest.model.nodes[1].x, 1 / 128);
    assert.match(await page.locator('#status').textContent(), /at least 0\.02 m/);
    assert.match(await page.locator('#section-results').textContent(), /—/);
    result.cases.push('exact-short-member-with-honest-numerical-panel-decline');

    const decimal = structuredClone(beam);
    decimal.nodes[1].x = 10; decimal.supports[1].t = 0.4;
    decimal.loads = [load('partial', 'beam', 0.2, 0.8), load('overlap', 'beam', 0.4, 1, -2),
        { id: 'couple', member: 'beam', kind: 'moment', t: 0.6, end: 1, fx: 0, fy: 0, mz: 3, qEnd: 0 }];
    const decimalLeft = await check(decimal, 'beam', 0.6, 'left');
    await select('beam', 0.6, 'right');
    const decimalRight = await accepted();
    assert.equal(decimalRight.artifact, first.artifact);
    assert.ok(decimalRight.revision > decimalLeft.revision);
    assert.ok(Math.abs(number(decimalRight.values.readouts[2]) - number(decimalLeft.values.readouts[2]) + 3) < 1e-10);
    assert.equal(decimalRight.sourceRequest.model.supports[1].t, 0.4);
    result.cases.push('offline-common-decimal-partial-overlap-support-and-couple-side');

    const resized = structuredClone(originalPortal);
    resized.nodes[1].y = resized.nodes[2].y = 3.25;
    resized.nodes[2].x = resized.nodes[3].x = 7.5;
    resized.members[0].EA = 3000000; resized.members[1].EI = 30000;
    resized.supports[0].kind = 'pin';
    resized.loads.push({ id: 'horizontal', member: 'BC', kind: 'force', t: 0, end: 1, fx: 7, fy: 0, mz: 0, qEnd: 0 });
    let changed = await check(resized, 'BC', 0.25);
    assert.equal(changed.sourceRequest.model.nodes[2].x, 7.5);
    assert.equal(changed.sourceRequest.model.supports[0].kind, 'pin');
    resized.loads[0].fy = resized.loads[0].qEnd = -7;
    changed = await check(resized, 'AB', 0.75);
    assert.equal(changed.sourceRequest.model.loads[0].fy, -7);
    assert.equal(changed.artifact, first.artifact);
    await check(originalPortal, 'BC');
    assert.deepEqual((await accepted()).values.readouts, originalResponse.values.readouts);
    result.cases.push('offline-resized-portal-load-material-restraint-and-query-edits');

    const unrestrained = structuredClone(beam);
    unrestrained.supports = []; unrestrained.loads = [];
    const mechanism = await check(unrestrained, 'beam', 0.5, 'left', 'mechanism');
    assert.equal(mechanism.values.loadWork.numerator, '0');
    assert.match(await page.locator('#portal-status').textContent(), /does not determine load compatibility/);
    unrestrained.loads = [{ id: 'work', member: 'beam', kind: 'force', t: 0, end: 1, fx: 1, fy: 1, mz: 1, qEnd: 0 }];
    const loadedMechanism = await check(unrestrained, 'beam', 0.5, 'left', 'mechanism');
    assert.notEqual(loadedMechanism.values.loadWork.numerator, '0');
    assert.match(await page.locator('#portal-status').textContent(), /incompatible with equilibrium/);
    result.cases.push('zero-load-mechanism-and-verified-incompatible-load');

    for (const edit of [model => { model.nodes[1].y = 0.1; },
        model => { model.supports[1].angle = 45; },
        model => { model.members[0].connectionB = { axial: 'rigid', transverse: 'rigid', rotation: 'free' }; }]) {
        const unsupported = structuredClone(beam); edit(unsupported);
        await importModel(unsupported); await select('beam');
        await page.waitForFunction(() => document.getElementById('portal-status').textContent.includes('Unsupported'));
        assert.equal(await page.locator('#portal-certificate').textContent(), '');
        assert.equal(await page.locator('#frame-export').isVisible(), false);
    }
    const oversized = structuredClone(beam); oversized.members[0].EA = Number.MIN_VALUE;
    await importModel(oversized); await select('beam');
    await page.waitForFunction(() => /Limit:|limit/.test(document.getElementById('portal-status').textContent));
    assert.equal(await page.locator('#portal-certificate').textContent(), '');
    result.cases.push('unsupported-and-arithmetic-limit-clear-acceptance');

    await check(beam, 'beam');
    for (const parameter of [0.25, 0.75, 0.5]) await select('beam', parameter);
    const reverted = await accepted();
    assert.equal(number(reverted.values.query.parameter), 0.5);
    await page.locator('#frame-parameter').fill('0.123456789');
    const precise = await accepted();
    assert.equal(number(precise.values.query.parameter), 0.123456789);
    await page.locator('#frame-parameter').fill('');
    assert.equal(await page.locator('#portal-certificate').textContent(), '');
    await page.locator('#frame-parameter').fill('0.5');
    const latest = await accepted();
    assert.equal(number(latest.values.query.parameter), 0.5);
    assert.equal(latest.artifact, first.artifact);
    assert.deepEqual(result.offlineRequests, []);
    result.offlineEditRequests = [...result.offlineRequests];
    const downloadPromise = page.waitForEvent('download');
    await page.locator('#frame-export').click();
    const exported = JSON.parse(await readFile(await (await downloadPromise).path(), 'utf8'));
    assert.equal(exported.packetDigest, latest.packetDigest);
    assert.equal(exported.inputDigest, latest.inputDigest);
    assert.equal(exported.packet, latest.packet);
    result.cases.push('offline-query-race-and-local-exact-certificate-export');
    await page.screenshot({ path: resolve(output, 'portal-accepted.png'), fullPage: true });

    const watchdog = await page.evaluate(async () => {
        const workerURL = URL.createObjectURL(new Blob([
            "postMessage({ready:true,isolated:crossOriginIsolated,artifact:'watchdog',bundle:'fixture',protocols:['frame']}); onmessage=()=>{for(;;){}};",
        ], { type: 'text/javascript' }));
        const runtime = new window.runtimeFixture.PortalRuntime(new URL(workerURL));
        try {
            await runtime.ready;
            const timed = await runtime.checkFrame(new Uint8Array([1]));
            const stopped = await runtime.checkFrame(new Uint8Array([1]));
            return [timed.state, stopped.state];
        } finally { runtime.dispose(); URL.revokeObjectURL(workerURL); }
    });
    assert.deepEqual(watchdog, ['timeout', 'reset-required']);
    // Creating the watchdog's local blob worker is recorded as a request by
    // Playwright, but it is not an HTTP request or a model upload.
    result.offlineNetworkRequests = result.offlineRequests.filter(url => /^https?:/.test(url));
    assert.deepEqual(result.offlineNetworkRequests, []);
    result.cases.push('generic-browser-worker-watchdog-and-reset-required');
    await setOffline(false);
    await page.locator('#portal-reset').click(); await accepted();
    await page.locator('#portal-deactivate').click(); await page.waitForURL(origin + base);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller), null);
    assert.deepEqual(await page.evaluate(async () => (await navigator.serviceWorker.getRegistrations()).map(registration => registration.scope)), [sentinelScope]);
    await page.evaluate(async scope => {
        for (const registration of await navigator.serviceWorker.getRegistrations()) if (registration.scope === scope) await registration.unregister();
    }, sentinelScope);
    result.cases.push('generic-reset-and-exact-scope-root-neighbor-cleanup');
    assert.deepEqual(result.errors, []);
    result.passed = true;
}
