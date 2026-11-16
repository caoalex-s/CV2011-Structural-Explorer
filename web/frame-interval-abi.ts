/** Copy the report after a successful compiled ABI call. This helper checks
 * memory bounds only; the caller must establish acceptance and request identity.
 */
export interface InclinedReportMemory {
    readonly HEAPU8: Uint8Array;
    _output_ptr(): number;
    _output_size(): number;
    _output_capacity(): number;
}

export function copyInclinedReport(runtime: InclinedReportMemory): Uint8Array {
    const pointer = runtime._output_ptr();
    const length = runtime._output_size();
    const capacity = runtime._output_capacity();
    if (!Number.isInteger(pointer) || pointer < 0 || pointer > 0xffffffff ||
        capacity !== 262144 || !Number.isInteger(length) || length <= 0 || length > capacity)
        throw Error('Invalid inclined report buffer bounds.');
    // Obtain the current view after the ABI call, which may grow WASM memory.
    const memory = runtime.HEAPU8;
    if (!(memory instanceof Uint8Array) || pointer + length > memory.byteLength)
        throw Error('Inclined report extends beyond current checker memory.');
    // Retain independent bytes before another checker call can reuse the buffer.
    return new Uint8Array(memory.subarray(pointer, pointer + length));
}
