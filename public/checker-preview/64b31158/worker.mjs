// Test-only browser worker. No rational arithmetic or candidate solving in JS.
const sha256 = async bytes => Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256', bytes)))
    .map(byte => byte.toString(16).padStart(2, '0')).join('');
const manifest = await (await fetch(new URL('./manifest.json', import.meta.url))).json();
const wasm = await (await fetch(new URL('./checker.wasm', import.meta.url))).arrayBuffer();
const javascript = await (await fetch(new URL('./checker.mjs', import.meta.url))).arrayBuffer();
if (await sha256(wasm) !== manifest['checker.wasm'] ||
    await sha256(javascript) !== manifest['checker.mjs']) throw new Error('Artifact digest mismatch');
const { default: createChecker } = await import('./checker.mjs');
const module = await createChecker({ wasmBinary: wasm });
if (module._checker_init() !== 1) throw new Error('Lean runtime initialization failed');
const pointer = module._input_ptr();
const capacity = module._input_capacity();

self.onmessage = async ({ data }) => {
    const { id, artifact, bytes, pointerOffset = 0, length = bytes.length, stall = false } = data;
    const inputDigest = await sha256(bytes);
    if (artifact !== manifest['checker.wasm']) {
        postMessage({ id, artifact, inputDigest, state: 'artifact-mismatch' });
        return;
    }
    // Only used to exercise the host timeout; never used for an ordinary check.
    if (stall) { for (;;) { /* terminated by the host watchdog */ } }
    if (bytes.length > capacity) {
        postMessage({ id, artifact, inputDigest, state: 'limit' });
        return;
    }
    module.HEAPU8.set(bytes, pointer);
    const start = performance.now();
    const code = module._checker_check(pointer + pointerOffset, length);
    const states = ['rejected', 'accepted', 'malformed', 'limit', 'uninitialized'];
    postMessage({ id, artifact, inputDigest, state: states[code] ?? 'error', code,
        milliseconds: performance.now() - start, memoryBytes: module.HEAPU8.byteLength });
};
postMessage({ ready: true, isolated: self.crossOriginIsolated, sharedArrayBuffer: typeof SharedArrayBuffer, artifact: manifest['checker.wasm'], capacity,
    memoryBytes: module.HEAPU8.byteLength });
