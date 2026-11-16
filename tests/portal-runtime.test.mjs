import test from 'node:test';
import assert from 'node:assert/strict';
import { PortalRuntime, sha256 } from '../web/portal-runtime.ts';

class WorkerFixture {
    static instances = [];
    sent = [];
    terminated = false;
    constructor() { WorkerFixture.instances.push(this); }
    postMessage(data) { this.sent.push(data); }
    terminate() { this.terminated = true; }
    ready(artifact = 'new-artifact', protocols = ['portal'], capabilities = []) {
        this.onmessage({ data: { ready: true, isolated: true, artifact, bundle: 'bundle-v1', protocols, capabilities } });
    }
}
globalThis.Worker = WorkerFixture;

test('an edit terminates an inclined request and a fresh worker can accept the next source', async () => {
    const runtime = new PortalRuntime(new URL('https://example.invalid/worker.mjs'));
    const worker = WorkerFixture.instances.at(-1);
    worker.ready('inclined-artifact', ['frame'], ['inclined-real-v1']); await runtime.ready;
    const pending = runtime.checkFrame(new Uint8Array([1]), 'inclined');
    await new Promise(resolve => setTimeout(resolve, 10));
    const old = worker.sent.at(-1);
    runtime.invalidate();
    assert.equal((await pending).state, 'stale');
    assert.equal(worker.terminated, true);
    assert.equal(runtime.needsReset, true);
    assert.equal(runtime.receive({ id: old.id, artifact: runtime.artifact, state: 'accepted',
        inputDigest: await sha256(old.bytes) }), false);
    assert.equal((await runtime.checkFrame(new Uint8Array([2]), 'inclined')).state, 'reset-required');
    runtime.dispose();
    const fresh = new PortalRuntime(new URL('https://example.invalid/worker.mjs'));
    const replacement = WorkerFixture.instances.at(-1);
    replacement.ready('inclined-artifact', ['frame'], ['inclined-real-v1']); await fresh.ready;
    const next = fresh.checkFrame(new Uint8Array([2]), 'inclined');
    await new Promise(resolve => setTimeout(resolve, 10));
    const current = replacement.sent.at(-1);
    fresh.receive({ id: current.id, artifact: fresh.artifact, state: 'accepted', inputDigest: await sha256(current.bytes) });
    assert.equal((await next).state, 'accepted');
    fresh.dispose();
});

test('older frame bundles cannot admit an inclined request', async () => {
    const runtime = new PortalRuntime(new URL('https://example.invalid/worker.mjs'));
    const worker = WorkerFixture.instances.at(-1);
    worker.ready('exact-artifact', ['frame'], ['affine-vertical-v1']); await runtime.ready;
    assert.equal(runtime.supportsInclinedFrames, false);
    assert.equal((await runtime.checkFrame(new Uint8Array([1]), 'inclined')).state, 'unsupported-runtime');
    assert.equal(worker.sent.length, 0);
    runtime.dispose();
});

test('digestless guard failures settle only the matching request and discard checked payloads', async () => {
    const runtime = new PortalRuntime(new URL('https://example.invalid/worker.mjs'));
    const worker = WorkerFixture.instances.at(-1);
    worker.ready(); await runtime.ready;
    const request = runtime.check(new Uint8Array([1]));
    await new Promise(resolve => setTimeout(resolve, 10));
    const { id } = worker.sent.at(-1);
    const identity = { id, artifact: runtime.artifact };
    assert.equal(runtime.receive({ ...identity, state: 'accepted' }), false);
    assert.equal(runtime.receive({ ...identity, state: 'limit', id: id - 1 }), false);
    assert.equal(runtime.receive({ ...identity, state: 'limit', artifact: 'old-artifact' }), false);
    assert.equal(runtime.receive({ ...identity, state: 'limit', inputDigest: 'wrong' }), false);
    assert.equal(runtime.receive({ ...identity, state: 'limit', message: 'Limit: oversized input.',
        checked: [{ numerator: '1', denominator: '1' }], interval: { forged: true } }), true);
    assert.deepEqual(await request, { ...identity, state: 'limit', message: 'Limit: oversized input.' });
    assert.equal(worker.terminated, false);
    runtime.dispose();
});

test('affine capability is explicit and absent from older generic runtime greetings', async () => {
    for (const supported of [false, true]) {
        const runtime = new PortalRuntime(new URL('https://example.invalid/worker.mjs'));
        const worker = WorkerFixture.instances.at(-1);
        worker.ready('frame-artifact', ['frame'], supported ? ['affine-vertical-v1'] : []);
        await runtime.ready;
        assert.equal(runtime.supportsFrames, true);
        assert.equal(runtime.supportsAffineFrames, supported);
        runtime.dispose();
    }
});

test('frame requests capture source and query bytes and require a generic bundle', async () => {
    const legacy = new PortalRuntime(new URL('https://example.invalid/worker.mjs'));
    const legacyWorker = WorkerFixture.instances.at(-1);
    legacyWorker.ready(); await legacy.ready;
    assert.equal((await legacy.checkFrame(new Uint8Array([1]))).state, 'unsupported-runtime');
    assert.equal(legacyWorker.sent.length, 0);
    legacy.dispose();

    const runtime = new PortalRuntime(new URL('https://example.invalid/worker.mjs'));
    const worker = WorkerFixture.instances.at(-1);
    worker.ready('generic-artifact', ['portal', 'frame']); await runtime.ready;
    const source = new TextEncoder().encode('{"model":{},"query":{"parameter":0.5}}');
    const original = new Uint8Array(source);
    const request = runtime.checkFrame(source);
    source.fill(0);
    await new Promise(resolve => setTimeout(resolve, 10));
    const packet = worker.sent.at(-1);
    assert.equal(packet.protocol, 'frame');
    assert.deepEqual(packet.bytes, original);
    const inputDigest = await sha256(original);
    assert.equal(runtime.receive({ state: 'accepted', id: packet.id, artifact: runtime.artifact,
        inputDigest: await sha256(source) }), false);
    runtime.receive({ state: 'accepted', id: packet.id, artifact: runtime.artifact, inputDigest });
    assert.equal((await request).state, 'accepted');
    runtime.dispose();
});

test('current packet, artifact and revision bind acceptance; late packets cannot survive reversion', async () => {
    const runtime = new PortalRuntime(new URL('https://example.invalid/worker.mjs'));
    const worker = WorkerFixture.instances.at(-1); worker.ready(); await runtime.ready;
    const first = runtime.check(new Uint8Array([1]));
    await new Promise(resolve => setTimeout(resolve, 10));
    const firstPacket = worker.sent[0];
    const second = runtime.check(new Uint8Array([2]));
    const reverted = runtime.check(new Uint8Array([1]));
    assert.equal((await first).state, 'stale'); assert.equal((await second).state, 'stale');
    await new Promise(resolve => setTimeout(resolve, 10));
    const packet = worker.sent.at(-1);
    const inputDigest = await sha256(packet.bytes);
    assert.equal(runtime.receive({ state: 'accepted', id: firstPacket.id, artifact: 'new-artifact', inputDigest }), false);
    assert.equal(runtime.receive({ state: 'accepted', id: packet.id, artifact: 'old-artifact', inputDigest }), false);
    assert.equal(runtime.receive({ state: 'accepted', id: packet.id, artifact: 'new-artifact', inputDigest: 'wrong' }), false);
    assert.equal(runtime.receive({ state: 'accepted', id: packet.id, artifact: 'new-artifact', inputDigest }), true);
    assert.equal((await reverted).state, 'accepted'); runtime.dispose();
});

test('watchdog terminates the worker, removes acceptance and requires a fresh instance', async () => {
    const runtime = new PortalRuntime(new URL('https://example.invalid/worker.mjs'));
    const worker = WorkerFixture.instances.at(-1); worker.ready(); await runtime.ready;
    assert.equal((await runtime.check(new Uint8Array([1]))).state, 'timeout');
    assert.equal(worker.terminated, true);
    assert.equal((await runtime.check(new Uint8Array([1]))).state, 'reset-required');
    runtime.dispose();
    const reset = new PortalRuntime(new URL('https://example.invalid/worker.mjs'));
    const replacement = WorkerFixture.instances.at(-1); replacement.ready('replacement'); await reset.ready;
    assert.equal(reset.artifact, 'replacement'); reset.dispose();
});

test('worker failure and a changed theorem bundle notify the display even while idle', async () => {
    for (const failure of ['worker', 'bundle']) {
        const runtime = new PortalRuntime(new URL('https://example.invalid/worker.mjs'));
        const worker = WorkerFixture.instances.at(-1);
        worker.ready(); await runtime.ready;
        const notices = [];
        runtime.onFailure = reason => notices.push(reason);
        if (failure === 'worker') worker.onerror();
        else worker.onmessage({ data: { ready: true, isolated: true, artifact: runtime.artifact, bundle: 'changed-tables-or-theorem' } });
        assert.equal(notices.length, 1);
        assert.equal(worker.terminated, true);
        assert.equal((await runtime.check(new Uint8Array([1]))).state, 'reset-required');
    }
});
