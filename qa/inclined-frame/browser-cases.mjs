/** Actual compiled runtime checks on a separate, isolated local CI origin.
 * These tests do not claim inclined main-workspace UI integration.
 */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { createServer } from 'node:http';
import { readFile, readdir } from 'node:fs/promises';
import { resolve, extname } from 'node:path';
import { pathToFileURL } from 'node:url';

const digest = bytes => createHash('sha256').update(bytes).digest('hex');
export async function runInclinedCases({ context, bundle, result }) {
    const directory = resolve('.data/live-portal/inclined-native');
    const fixtures = JSON.parse(await readFile(resolve(directory, 'manifest.json'), 'utf8'));
    const manifestBytes = await readFile(resolve(bundle, 'manifest.json'));
    const manifest = JSON.parse(manifestBytes);
    const { decodeAcceptedIntervalReport } = await import(pathToFileURL(resolve(bundle, 'frame-interval-result.js')).href);
    // Immutable served bytes bind both verification fetches and later imports.
    const served = new Map();
    for (const name of await readdir(bundle)) served.set(name, await readFile(resolve(bundle, name)));
    served.set('abi-fixture.mjs', await readFile('qa/inclined-frame/abi-fixture.mjs'));
    served.set('', Buffer.from('<!doctype html><title>Inclined runtime fixture</title>'));
    const requested = new Set();
    const types = { '.mjs': 'text/javascript', '.js': 'text/javascript', '.wasm': 'application/wasm', '.json': 'application/json' };
    const server = createServer((request, response) => {
        const name = new URL(request.url, 'http://localhost').pathname.slice(1);
        if (!served.has(name)) { response.writeHead(404).end(); return; }
        requested.add(name);
        response.writeHead(200, { 'Content-Type': types[extname(name)] ?? 'text/html',
            'Cross-Origin-Opener-Policy': 'same-origin', 'Cross-Origin-Embedder-Policy': 'require-corp',
            'Cache-Control': 'no-store' });
        response.end(served.get(name));
    });
    await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
    const page = await context.newPage();
    const measurements = { abi: [], worker: [], servedAssets: {}, mainInclinedUiVerified: false };
    result.inclined = measurements;
    try {
        await page.goto(`http://127.0.0.1:${server.address().port}/`);
        assert.equal(await page.evaluate(() => crossOriginIsolated), true);
        await page.evaluate(() => {
            const workers = new Map();
            window.inclinedHarness = {
                async start(name, file) {
                    const worker = new Worker(new URL(file, location.href), { type: 'module' });
                    workers.set(name, worker);
                    return new Promise((resolve, reject) => {
                        const timer = setTimeout(() => { worker.terminate(); reject(Error('Worker startup deadline')); }, 30000);
                        worker.onerror = event => { clearTimeout(timer); worker.terminate(); reject(Error(event.message)); };
                        worker.onmessage = ({ data }) => { if (data.ready) { clearTimeout(timer); resolve(data); } };
                    });
                },
                async call(name, data, deadline = 180000, mutateAfterPost = false) {
                    const worker = workers.get(name);
                    if (!worker) throw Error('Missing fixture worker');
                    return new Promise(resolve => {
                        const timer = setTimeout(() => {
                            worker.onmessage = null; worker.terminate(); workers.delete(name);
                            resolve({ timedOut: true });
                        }, deadline);
                        worker.onerror = event => { clearTimeout(timer); worker.terminate(); workers.delete(name); resolve({ error: event.message }); };
                        worker.onmessage = ({ data }) => {
                            clearTimeout(timer); worker.onmessage = null;
                            if (data.report instanceof Uint8Array) data.report = Array.from(data.report);
                            if (data.packet instanceof Uint8Array) data.packet = Array.from(data.packet);
                            resolve(data);
                        };
                        worker.postMessage(data);
                        if (mutateAfterPost) data.bytes.fill(0);
                    });
                },
                stop() { for (const worker of workers.values()) worker.terminate(); workers.clear(); },
            };
        });
        const start = (name, file) => page.evaluate(({ name, file }) => window.inclinedHarness.start(name, file), { name, file });
        const abi = async (bytes, extra = {}) => {
            const value = await page.evaluate(({ bytes, extra }) => window.inclinedHarness.call('abi',
                { bytes: new Uint8Array(bytes), ...extra }), { bytes: Array.from(bytes), extra });
            assert(!value.timedOut && !value.error, JSON.stringify(value));
            return value;
        };
        const ready = await start('abi', 'abi-fixture.mjs');
        assert.equal(ready.uninitialized, 4);
        assert.equal(ready.isolated, true);
        assert.equal(ready.inputCapacity, 1048576);
        assert.equal(ready.outputCapacity, 262144);
        for (const fixture of fixtures) {
            const packet = await readFile(resolve(directory, fixture.name + '.txt'));
            assert.equal(digest(packet), fixture.sha256);
            const value = await abi(packet);
            if (fixture.expected === 'accept') {
                assert.equal(value.code, 1, fixture.name);
                const expected = await readFile(resolve(directory, fixture.name + '.report'));
                assert.deepEqual(Buffer.from(value.report), expected, fixture.name);
            } else {
                assert.notEqual(value.code, 1, fixture.name);
                assert.equal(value.outputSize, 0, fixture.name);
            }
            measurements.abi.push({ name: fixture.name, code: value.code, elapsedMs: value.elapsedMs, memoryBytes: value.memoryBytes });
        }
        const baseline = await readFile(resolve(directory, 'irrational-cantilever.txt'));
        const baselineReport = await readFile(resolve(directory, 'irrational-cantilever.report'));
        await abi(baseline);
        const wrongPointer = await abi(baseline, { pointerOffset: 1 });
        assert.equal(wrongPointer.code, 2); assert.equal(wrongPointer.outputSize, 0);
        await abi(baseline);
        const exact = await abi(await readFile('.data/general-frame-packets/1_two_spans.packet'));
        assert.equal(exact.code, 1); assert.equal(exact.outputSize, 0);
        await abi(baseline);
        const portal = await abi(Buffer.from(Array.from({ length: 42 }, (_, i) => i % 2 ? '1' : '0').join('\n')));
        assert.equal(portal.code, 1); assert.equal(portal.outputSize, 0);
        const growth = await page.evaluate(() => window.inclinedHarness.call('abi', { action: 'grow' }));
        assert(growth.after > growth.before, JSON.stringify(growth));
        assert.deepEqual(Buffer.from((await abi(baseline)).report), baselineReport);
        measurements.memoryGrowth = growth;
        result.cases.push('inclined-actual-wasm-native-report-equality-rejections-old-routes-stale-output-memory-growth');

        const checkerReady = await start('checker', 'worker.mjs');
        assert.equal(checkerReady.isolated, true);
        assert.equal(checkerReady.artifact, manifest.files['checker.wasm']);
        assert.equal(checkerReady.bundle, digest(manifestBytes));
        assert(checkerReady.capabilities.includes('inclined-real-v1'));
        let requestId = 0;
        const worker = async (bytes, options = {}) => {
            const id = ++requestId;
            const started = performance.now();
            const value = await page.evaluate(({ id, artifact, bytes, options }) => {
                const data = { id, artifact, protocol: 'frame', bytes: new Uint8Array(bytes) };
                if (options.shared) data.bytes = new Uint8Array(new SharedArrayBuffer(8));
                if (options.malformed) data.bytes = new ArrayBuffer(8);
                return window.inclinedHarness.call('checker', data, options.deadline ?? 180000, options.mutate);
            }, { id, artifact: checkerReady.artifact, bytes: Array.from(bytes), options });
            if (!value.timedOut) { assert.equal(value.id, id); assert.equal(value.artifact, checkerReady.artifact); }
            return { value, elapsedMs: performance.now() - started };
        };
        for (const fixture of fixtures.filter(item => item.expected === 'accept')) {
            const bytes = await readFile(resolve(directory, fixture.name + '.request.json'));
            assert.equal(digest(bytes), fixture.requestSha256);
            const { value, elapsedMs } = await worker(bytes, { mutate: true });
            assert.equal(value.state, 'accepted', JSON.stringify(value));
            assert.equal(value.frameProtocol, 'inclined');
            assert.equal(value.inputDigest, digest(bytes));
            assert.equal(value.packetDigest, fixture.sha256);
            assert.equal(digest(Buffer.from(value.packet)), fixture.sha256);
            const report = await readFile(resolve(directory, fixture.name + '.report'));
            assert.equal(value.reportDigest, digest(report));
            assert.deepEqual(Buffer.from(value.report), report);
            assert.deepEqual(value.interval, decodeAcceptedIntervalReport(report));
            measurements.worker.push({ name: fixture.name, elapsedMs, memoryBytes: value.memoryBytes });
        }
        for (const options of [{ shared: true }, { malformed: true }]) {
            const { value } = await worker(new Uint8Array(), options);
            assert.equal(value.state, 'inconclusive'); assert.equal(value.inputDigest, undefined);
        }
        const oversized = (await worker(new Uint8Array(1048577))).value;
        assert.equal(oversized.state, 'limit'); assert.equal(oversized.inputDigest, undefined);
        const originalRequest = await readFile(resolve(directory, 'irrational-cantilever.request.json'));
        const changed = JSON.parse(originalRequest); changed.model.loads[0].fy = -8;
        const changedBytes = Buffer.from(JSON.stringify(changed));
        const changedResult = (await worker(changedBytes)).value;
        assert.equal(changedResult.state, 'accepted');
        assert.equal(changedResult.inputDigest, digest(changedBytes));
        assert.notEqual(changedResult.reportDigest, digest(baselineReport));
        const cardinal = JSON.parse(originalRequest); cardinal.model.nodes[1].y = 0;
        const cardinalResult = (await worker(Buffer.from(JSON.stringify(cardinal)))).value;
        assert.equal(cardinalResult.state, 'accepted'); assert.equal(cardinalResult.frameProtocol, 'exact');
        assert.equal(cardinalResult.report, undefined);
        result.cases.push('inclined-worker-original-snapshot-packet-report-digests-preallocation-guards-exact-route');

        const timeoutBytes = await readFile(resolve(directory, 'roller-interior-left.request.json'));
        assert.equal((await worker(timeoutBytes, { deadline: 1 })).value.timedOut, true);
        await start('checker', 'worker.mjs');
        assert.equal((await worker(originalRequest)).value.state, 'accepted');
        measurements.terminationAndRestart = true;
        const allocation = await page.evaluate(() => window.inclinedHarness.call('abi', { action: 'allocation-failure' }));
        assert(allocation.allocationFailed || (allocation.errorName === 'RuntimeError' &&
            /out of memory|Cannot enlarge memory|OOM|Aborted/i.test(allocation.error)), JSON.stringify(allocation));
        measurements.boundedAllocationFailure = allocation;
        result.cases.push('inclined-worker-deadline-termination-restart-and-bounded-wasm-allocation-failure');
        for (const [name, expected] of Object.entries(manifest.files)) {
            assert(requested.has(name), 'Runtime asset was not requested: ' + name);
            assert.equal(digest(served.get(name)), expected);
            measurements.servedAssets[name] = expected;
        }
        assert.equal(digest(served.get('worker.mjs')), manifest.workerSha256);
    } finally {
        await page.evaluate(() => window.inclinedHarness?.stop()).catch(() => {});
        await page.close();
        server.close();
    }
}
