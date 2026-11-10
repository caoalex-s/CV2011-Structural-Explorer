// CI-only public portal fixtures. No private model, external service, or deployment.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { createServer } from 'node:http';
import { readFile, writeFile, mkdir, copyFile } from 'node:fs/promises';
import { resolve, extname, dirname } from 'node:path';
import { spawnSync } from 'node:child_process';
import { chromium } from 'playwright';

assert.equal(process.env.GITHUB_ACTIONS, 'true');
assert.equal(process.platform, 'linux');
const [assets, source] = process.argv.slice(2);
const root = process.cwd();
const output = dirname(assets);
const bundle = resolve('public/portal-checker/bundle');
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
await mkdir(bundle, { recursive: true });
const files = {};
for (const name of ['checker.wasm', 'checker.mjs', 'checker.worker.js', 'checker.mjs.symbols']) {
    const bytes = await readFile(resolve(assets, name));
    files[name] = digest(bytes);
    await writeFile(resolve(bundle, name), bytes);
}
await copyFile(resolve(source, 'worker.mjs'), resolve(bundle, 'worker.mjs'));
const proofFiles = {};
for (const name of ['PortalChecker.lean', 'PortalTables.lean', 'PortalSoundness.lean', 'PortalFramePilot.lean', 'lean-toolchain', 'lake-manifest.json']) {
    proofFiles[name] = digest(await readFile(resolve('proofs', name)));
}
const manifest = { status: 'proved-compiled', theorem: 'PortalSoundness.acceptance_actual_portal',
    files, proofFiles, workerSha256: digest(await readFile(resolve(bundle, 'worker.mjs'))),
    abiSha256: digest(await readFile(resolve(source, 'abi.c'))),
    axiomAuditSha256: digest(await readFile('.data/live-portal-build/axiom-audit.json')),
    trust: 'Pinned Lean 4.19/C/Emscripten compilation, runtime, decoder and input binding. No kernel invocation per edit.' };
await writeFile(resolve(bundle, 'manifest.json'), JSON.stringify(manifest, null, 2) + '\n');
assert.equal(spawnSync('node', ['scripts/build.mjs'], { stdio: 'inherit' }).status, 0);

const dist = resolve('dist');
const base = '/CV2011-Structural-Explorer/';
const types = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript', '.wasm': 'application/wasm', '.css': 'text/css', '.json': 'application/json' };
const server = createServer(async (request, response) => {
    try {
        const url = new URL(request.url, 'http://localhost');
        if (!url.pathname.startsWith(base)) { response.writeHead(404).end(); return; }
        const relative = decodeURIComponent(url.pathname.slice(base.length));
        const path = resolve(dist, relative + (relative.endsWith('/') ? 'index.html' : ''));
        if (!path.startsWith(dist + '/')) { response.writeHead(403).end(); return; }
        const bytes = await readFile(path);
        response.writeHead(200, { 'Content-Type': types[extname(path)] ?? 'application/octet-stream', 'Cache-Control': 'no-store' });
        response.end(bytes);
    } catch { response.writeHead(404).end(); }
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const origin = `http://127.0.0.1:${server.address().port}`;
const url = origin + base + 'portal-checker/';
const browser = await chromium.launch({ headless: true });
const context = await browser.newContext({ acceptDownloads: true });
await context.tracing.start({ screenshots: true, snapshots: true, sources: false });
const page = await context.newPage();
const result = { passed: false, browser: browser.version(), cases: [], errors: [], offlineRequests: [] };
let offline = false;
page.on('pageerror', error => result.errors.push(String(error)));
context.on('request', request => { if (offline) result.offlineRequests.push(request.url()); });
async function accepted() {
    await page.waitForFunction(() => document.getElementById('portal-status')?.textContent === 'Accepted by the compiled proved checker.');
    return JSON.parse(await page.locator('#portal-certificate').textContent());
}
async function importModel(model) {
    await page.locator('#model-file').setInputFiles({ name: 'public-portal.json', mimeType: 'application/json', buffer: Buffer.from(JSON.stringify({ version: 2, model })) });
}
try {
    await page.goto(origin + base);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller), null);
    await page.locator('a[href="portal-checker/"]').click();
    assert.equal(page.url(), url);
    assert.equal(await page.evaluate(() => crossOriginIsolated), false);
    await page.locator('#portal-amplitude').fill('-5');
    const model = await page.evaluate(() => JSON.parse(localStorage.getItem('cv2011-checked-portal-model/v1')));
    await page.locator('#section-position').evaluate(element => { element.value = '400'; });
    await page.locator('#section-position').dispatchEvent('input');
    await Promise.all([page.waitForNavigation(), page.locator('#portal-activate').click()]);
    assert.equal(await page.locator('#section-position').inputValue(), '400');
    await page.waitForFunction(() => document.getElementById('portal-status').textContent.includes('Unsupported query'));
    assert.equal(await page.locator('#portal-certificate').textContent(), '');
    await page.locator('#section-position').evaluate(element => { element.value = '500'; });
    await page.locator('#section-position').dispatchEvent('input');
    const first = await accepted();
    assert.equal(await page.evaluate(() => crossOriginIsolated), true);
    assert.deepEqual(first.amplitude, { numerator: '-5', denominator: '1' });
    assert.match(await page.locator('#portal-readouts').textContent(), /11\.262.*-1\.720/s);
    await page.screenshot({ path: resolve(output, 'portal-accepted.png'), fullPage: true });
    assert.deepEqual(await page.evaluate(() => JSON.parse(localStorage.getItem('cv2011-checked-portal-model/v1'))), model);
    result.cases.push('baseline-and-activation-state');

    // Load the test entry once before cutting the network. ABI calls below use
    // the actual newly compiled module, including malformed pointer/length tests.
    await page.evaluate(async () => {
        const { default: createChecker } = await import('./bundle/checker.mjs');
        window.abiFixture = await createChecker();
        window.candidateFixture = await import('./portal-candidate.js');
        if (window.abiFixture._checker_init() !== 1) throw Error('Fixture initialization');
    });
    const neighbor = await context.newPage();
    await neighbor.goto(origin + base);
    assert.equal(await neighbor.evaluate(() => navigator.serviceWorker.controller), null);
    await neighbor.close();
    await context.setOffline(true); offline = true;
    for (const value of [-12, 5, 0, 0.1]) {
        await page.locator('#portal-amplitude').fill(String(value));
        const certificate = await accepted();
        assert.ok(certificate.request > first.request);
        if (value === 0.1) assert.deepEqual(certificate.amplitude, { numerator: '3602879701896397', denominator: '36028797018963968' });
    }
    for (const value of [Number.MIN_VALUE, Number.MAX_VALUE]) {
        await page.locator('#portal-amplitude').fill(String(value));
        await page.waitForFunction(() => document.getElementById('portal-status').textContent.includes('Limit exceeded'));
        assert.equal(await page.locator('#portal-certificate').textContent(), '');
    }
    result.cases.push('signed-zero-binary64-and-resource-limits');

    const abi = await page.evaluate(() => {
        const module = window.abiFixture, fixture = window.candidateFixture;
        const pointer = module._input_ptr();
        const run = bytes => { module.HEAPU8.set(bytes, pointer); return module._checker_check(pointer, bytes.length); };
        const candidate = fixture.portalCandidate(-5), good = fixture.encodeCandidate(candidate);
        const codes = [run(good)];
        for (let i = 1; i < 21; i++) {
            const changed = structuredClone(candidate); changed[i].numerator = String(BigInt(changed[i].numerator) + 1n);
            codes.push(run(fixture.encodeCandidate(changed)));
        }
        const order = structuredClone(candidate); [order[4], order[5]] = [order[5], order[4]];
        codes.push(run(fixture.encodeCandidate(order)));
        const sign = structuredClone(candidate); sign[0].numerator = '5'; codes.push(run(fixture.encodeCandidate(sign)));
        const malformed = new TextEncoder().encode(new TextDecoder().decode(good).replace(/\n1\n/, '\n0\n'));
        return { codes, malformed: run(malformed), pointer: module._checker_check(pointer + 1, good.length),
            oversized: module._checker_check(pointer, module._input_capacity() + 1) };
    });
    assert.equal(abi.codes[0], 1);
    assert.ok(abi.codes.slice(1).every(code => code === 0));
    assert.equal(abi.malformed, 2); assert.equal(abi.pointer, 2); assert.equal(abi.oversized, 3);
    result.cases.push('actual-abi-all-output-tampering-and-malformed-rejection');

    const edits = [m => m.loads[0].fy = -6, m => m.loads[0].t = 0.1,
        m => m.loads[0].member = 'AB', m => m.loads.push({ ...m.loads[0], id: 'extra' }),
        m => m.nodes[0].x = 0.1, m => m.members[0].EI++, m => m.supports[0].kind = 'pin',
        m => m.members.reverse(), m => m.nodes[1].referenceMember = 'BC',
        m => m.members[0].connectionB = { axial: 'rigid', transverse: 'rigid', rotation: 'free' }];
    for (const edit of edits) {
        const changed = structuredClone(model); edit(changed); await importModel(changed);
        await page.waitForFunction(() => document.getElementById('portal-status').textContent.includes('Unsupported'));
        assert.equal(await page.locator('#portal-certificate').textContent(), '');
    }
    await importModel(model);
    // Import preserves the ordinary query control; select the explicitly checked query.
    await page.locator('#section-member').selectOption('BC');
    await accepted();
    await page.locator('#section-position').evaluate(element => { element.value = '400'; });
    await page.locator('#section-position').dispatchEvent('input');
    assert.equal(await page.locator('#portal-certificate').textContent(), '');
    await page.locator('#section-position').evaluate(element => { element.value = '500'; }); await page.locator('#section-position').dispatchEvent('input');
    await accepted();
    result.cases.push('unsupported-edits-query-invalidation-and-restoration');
    for (const value of ['-7', '9', '-5']) await page.locator('#portal-amplitude').fill(value);
    const latest = await accepted();
    assert.deepEqual(latest.amplitude, { numerator: '-5', denominator: '1' });
    assert.deepEqual(result.offlineRequests, []);
    result.cases.push('rapid-edit-revert-current-result-offline');
    const watchdog = await page.evaluate(async () => {
        const { PortalRuntime } = await import('./portal-runtime.js');
        // Test-only stalled browser worker exercises the production host's
        // watchdog without introducing a stall command into the shipped ABI.
        const workerURL = URL.createObjectURL(new Blob([
            "postMessage({ready:true,isolated:crossOriginIsolated,artifact:'watchdog-fixture',bundle:'fixture'}); onmessage=()=>{for(;;){}};",
        ], { type: 'text/javascript' }));
        const runtime = new PortalRuntime(new URL(workerURL));
        try { await runtime.ready; return await runtime.check(new Uint8Array([1])); }
        finally { runtime.dispose(); URL.revokeObjectURL(workerURL); }
    });
    assert.equal(watchdog.state, 'timeout');
    result.cases.push('browser-worker-watchdog');
    const downloadPromise = page.waitForEvent('download');
    await page.locator('#export-model').click();
    const download = await downloadPromise;
    const exported = JSON.parse(await readFile(await download.path(), 'utf8'));
    assert.equal(exported.model.loads[0].fy, -5);
    assert.equal(exported.model.loads[0].qEnd, -5);
    result.cases.push('local-model-export');
    offline = false; await context.setOffline(false);
    await page.locator('#portal-reset').click(); await accepted();
    await page.locator('#portal-deactivate').click(); await page.waitForURL(origin + base);
    assert.equal(await page.evaluate(() => navigator.serviceWorker.controller), null);
    assert.deepEqual(await page.evaluate(async () => (await navigator.serviceWorker.getRegistrations()).map(r => r.scope)), []);
    result.cases.push('reset-exact-scope-cleanup-root-neighbor');
    assert.deepEqual(result.errors, []);
    result.passed = true;
} catch (error) { result.failure = String(error.stack ?? error); throw error; }
finally {
    await context.setOffline(false);
    await page.evaluate(async scope => { for (const registration of await navigator.serviceWorker.getRegistrations()) if (registration.scope === scope) await registration.unregister(); }, url).catch(error => { result.cleanupError = String(error); });
    await context.tracing.stop({ path: resolve(output, 'browser-trace.zip') });
    await writeFile(resolve(output, 'browser-results.json'), JSON.stringify(result, null, 2) + '\n');
    await browser.close(); server.close();
}
