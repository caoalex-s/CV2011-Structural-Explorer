import test from 'node:test';
import assert from 'node:assert/strict';
import { captureCheckerBytes } from '../web/frame-worker-bytes.ts';

test('request snapshot owns only the selected bytes before asynchronous work', () => {
    const original = new Uint8Array([0, 65, 66, 0]);
    const snapshot = captureCheckerBytes(original.subarray(1, 3), 2);
    original.fill(0);
    assert.deepEqual([...snapshot], [65, 66]);
    assert.equal(captureCheckerBytes(new Uint8Array(1048576), 1048576).length, 1048576);
});

test('malformed, shared and oversized byte containers fail before snapshot creation', () => {
    for (const value of [null, undefined, {}, [65], 'A', new ArrayBuffer(1), new DataView(new ArrayBuffer(1))])
        assert.throws(() => captureCheckerBytes(value, 1048576), /Malformed/);
    assert.throws(() => captureCheckerBytes(new Uint8Array(new SharedArrayBuffer(1)), 1048576), /Malformed/);
    assert.throws(() => captureCheckerBytes(new Uint8Array(1048577), 1048576), /Limit:/);
    for (const capacity of [0, -1, 1.5, NaN, 1048577])
        assert.throws(() => captureCheckerBytes(new Uint8Array(1), capacity), /capacity/);
});
