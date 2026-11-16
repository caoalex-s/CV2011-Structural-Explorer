import test from 'node:test';
import assert from 'node:assert/strict';
import { copyInclinedReport } from '../web/frame-interval-abi.ts';

function memoryFixture() {
    return { HEAPU8: new Uint8Array([0, 65, 66, 0]),
        _output_ptr: () => 1, _output_size: () => 2, _output_capacity: () => 262144 };
}

test('report copy reads the refreshed memory view and owns its bytes', () => {
    const runtime = memoryFixture();
    const oldView = runtime.HEAPU8;
    runtime._output_size = () => {
        runtime.HEAPU8 = new Uint8Array([0, 67, 68, 0, 0, 0, 0, 0]);
        return 2;
    };
    const report = copyInclinedReport(runtime);
    assert.deepEqual([...report], [67, 68]);
    runtime.HEAPU8.fill(0);
    oldView.fill(0);
    assert.deepEqual([...report], [67, 68], 'Later calls cannot mutate the captured report.');
});

test('empty, oversized, invalid and out-of-memory report ranges are rejected', () => {
    for (const length of [0, -1, 262145, 1.5, NaN])
        assert.throws(() => copyInclinedReport({ ...memoryFixture(), _output_size: () => length }), /bounds/);
    for (const pointer of [-1, 0x100000000, 1.5, NaN])
        assert.throws(() => copyInclinedReport({ ...memoryFixture(), _output_ptr: () => pointer }), /bounds/);
    assert.throws(() => copyInclinedReport({ ...memoryFixture(), _output_ptr: () => 3 }), /memory/);
    assert.throws(() => copyInclinedReport({ ...memoryFixture(), _output_capacity: () => 262145 }), /bounds/);
});

test('the exact output capacity is allowed and typed-array subclasses cannot alias the copy', () => {
    const memory = Buffer.alloc(262145, 65);
    const report = copyInclinedReport({ ...memoryFixture(), HEAPU8: memory, _output_size: () => 262144 });
    assert.equal(report.length, 262144);
    memory.fill(0);
    assert.equal(report[0], 65);
    assert.equal(report.at(-1), 65);
});
