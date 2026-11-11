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
    ready(artifact = 'new-artifact') { this.onmessage({ data: { ready: true, isolated: true, artifact, bundle: 'bundle-v1' } }); }
}
globalThis.Worker = WorkerFixture;

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
