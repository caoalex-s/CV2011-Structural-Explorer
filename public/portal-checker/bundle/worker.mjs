// Trusted loader and ABI result binding, using the accepted isolated worker path.
const hash = async bytes => [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))]
    .map(byte => byte.toString(16).padStart(2, '0')).join('');
const manifestBytes = await (await fetch(new URL('./manifest.json', import.meta.url))).arrayBuffer();
const manifest = JSON.parse(new TextDecoder().decode(manifestBytes));
if (manifest.theorem !== 'PortalSoundness.acceptance_actual_portal' || manifest.status !== 'proved-compiled') throw Error('Unproved checker bundle');
const assets = {};
for (const name of ['checker.wasm', 'checker.mjs', 'checker.worker.js', 'checker.mjs.symbols']) {
    const response = await fetch(new URL(name, import.meta.url));
    if (!response.ok) throw Error('Missing checker asset');
    assets[name] = await response.arrayBuffer();
    if (await hash(assets[name]) !== manifest.files[name]) throw Error('Checker asset identity changed');
}
const { default: createChecker } = await import('./checker.mjs');
const module = await createChecker({ wasmBinary: assets['checker.wasm'] });
if (module._checker_init() !== 1) throw Error('Lean runtime initialization failed');
const pointer = module._input_ptr(), capacity = module._input_capacity();
self.onmessage = async ({ data }) => {
    const { id, artifact } = data;
    const bytes = new Uint8Array(data.bytes);
    const inputDigest = await hash(bytes);
    if (artifact !== manifest.files['checker.wasm']) { postMessage({ id, artifact, inputDigest, state: 'artifact-mismatch' }); return; }
    if (bytes.length > capacity) { postMessage({ id, artifact, inputDigest, state: 'limit' }); return; }
    module.HEAPU8.set(bytes, pointer);
    const code = module._checker_check(pointer, bytes.length);
    const state = ['rejected', 'accepted', 'malformed', 'limit', 'uninitialized'][code] ?? 'error';
    // The returned values are the exact packet accepted by Lean, not an
    // unrelated caller object or values from the numerical diagram renderer.
    const fields = code === 1 ? new TextDecoder().decode(bytes).split('\n') : [];
    const checked = code === 1 ? Array.from({ length: 21 }, (_, i) => ({ numerator: fields[2 * i], denominator: fields[2 * i + 1] })) : undefined;
    postMessage({ id, artifact, inputDigest, state, checked, memoryBytes: module.HEAPU8.byteLength });
};
postMessage({ ready: true, isolated: crossOriginIsolated, artifact: manifest.files['checker.wasm'], bundle: await hash(manifestBytes), capacity });
