/** Linux browser-test worker for the actual compiled ABI, never a shipped entry. */
import createChecker from './checker.mjs';
import { copyInclinedReport } from './frame-interval-abi.js';
const runtime = await createChecker();
const uninitialized = runtime._checker_check(runtime._input_ptr(), 0);
if (runtime._checker_init() !== 1) throw Error('ABI fixture initialization failed.');
self.onmessage = ({ data }) => {
    try {
        if (data.action === 'grow') {
            const before = runtime.HEAPU8.byteLength;
            const allocation = runtime._malloc(before + 65536);
            if (!allocation) throw Error('Memory growth allocation failed.');
            const after = runtime.HEAPU8.byteLength;
            runtime._free(allocation);
            postMessage({ before, after });
            return;
        }
        if (data.action === 'allocation-failure') {
            const allocation = runtime._malloc(0x7fffffff);
            if (allocation) runtime._free(allocation);
            postMessage({ allocationFailed: allocation === 0 });
            return;
        }
        const bytes = new Uint8Array(data.bytes);
        const pointer = runtime._input_ptr();
        if (bytes.length <= runtime._input_capacity()) runtime.HEAPU8.set(bytes, pointer);
        const started = performance.now();
        const code = runtime._checker_check(data.pointerOffset === undefined ? pointer : pointer + data.pointerOffset,
            data.length === undefined ? bytes.length : data.length);
        const elapsedMs = performance.now() - started;
        const outputSize = runtime._output_size();
        const report = outputSize ? copyInclinedReport(runtime) : new Uint8Array();
        postMessage({ code, outputSize, report, elapsedMs, memoryBytes: runtime.HEAPU8.byteLength });
    } catch (error) {
        postMessage({ error: String(error), errorName: error?.name });
    }
};
postMessage({ ready: true, uninitialized, isolated: crossOriginIsolated,
    inputCapacity: runtime._input_capacity(), outputCapacity: runtime._output_capacity() });
