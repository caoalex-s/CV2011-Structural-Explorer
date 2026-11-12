// Trusted loader and ABI result binding, using the accepted isolated worker path.
const hash = async bytes => [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))]
    .map(byte => byte.toString(16).padStart(2, '0')).join('');
const manifestBytes = await (await fetch(new URL('./manifest.json', import.meta.url))).arrayBuffer();
const manifest = JSON.parse(new TextDecoder().decode(manifestBytes));
const generic = manifest.theorem === 'RationalFrameSoundness.acceptance_actual_frame';
if ((!generic && manifest.theorem !== 'PortalSoundness.acceptance_actual_portal') || manifest.status !== 'proved-compiled') throw Error('Unproved checker bundle');
const assets = {};
const codeAssets = ['checker.wasm', 'checker.mjs', 'checker.worker.js', 'checker.mjs.symbols'];
if (generic) codeAssets.push('frame-rational.js', 'model-evidence.js', 'frame-candidate.js', 'frame-packet.js', 'frame-result.js');
for (const name of codeAssets) {
    const response = await fetch(new URL(name, import.meta.url));
    if (!response.ok) throw Error('Missing checker asset');
    assets[name] = await response.arrayBuffer();
    if (await hash(assets[name]) !== manifest.files[name]) throw Error('Checker asset identity changed');
}
const { default: createChecker } = await import('./checker.mjs');
const module = await createChecker({ wasmBinary: assets['checker.wasm'] });
if (module._checker_init() !== 1) throw Error('Lean runtime initialization failed');
const pointer = module._input_ptr(), capacity = module._input_capacity();
const frameCode = generic ? await import('./frame-candidate.js') : null;
const packetCode = generic ? await import('./frame-packet.js') : null;
const resultCode = generic ? await import('./frame-result.js') : null;
const candidates = frameCode ? new frameCode.FrameCandidates() : null;
self.onmessage = async ({ data }) => {
    const { id, artifact } = data;
    const bytes = new Uint8Array(data.bytes);
    const inputDigest = await hash(bytes);
    if (artifact !== manifest.files['checker.wasm']) { postMessage({ id, artifact, inputDigest, state: 'artifact-mismatch' }); return; }
    if (bytes.length > capacity) { postMessage({ id, artifact, inputDigest, state: 'limit' }); return; }
    try {
        let packet = bytes;
        if (data.protocol === 'frame') {
            if (!generic) throw Error('Unsupported: this installed bundle does not check general frames.');
            const source = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(bytes));
            if (!source || typeof source !== 'object' || Array.isArray(source) ||
                Object.keys(source).some(key => key !== 'model' && key !== 'query') || !source.model || !source.query)
                throw Error('Malformed frame request.');
            const frame = frameCode.compileFrame(source.model, source.query);
            // The serializer reads the captured source again. Candidate-owned
            // arrays supply witnesses only; Lean derives K/F/C and point order.
            packet = packetCode.framePacket(source.model, source.query, candidates.produce(frame));
        }
        if (packet.length > capacity) { postMessage({ id, artifact, inputDigest, state: 'limit' }); return; }
        module.HEAPU8.set(packet, pointer);
        const code = module._checker_check(pointer, packet.length);
        const state = ['rejected', 'accepted', 'malformed', 'limit', 'uninitialized'][code] ?? 'error';
        // Only the bytes accepted by this ABI call supply displayed values.
        let checked, frame, packetDigest;
        if (code === 1 && data.protocol === 'frame') {
            frame = resultCode.decodeAcceptedFramePacket(packet);
            packetDigest = await hash(packet);
        } else if (code === 1) {
            const fields = new TextDecoder().decode(packet).split('\n');
            checked = Array.from({ length: 21 }, (_, i) => ({ numerator: fields[2 * i], denominator: fields[2 * i + 1] }));
        }
        postMessage({ id, artifact, inputDigest, state, checked, frame, packetDigest,
            packet: code === 1 && data.protocol === 'frame' ? packet : undefined, memoryBytes: module.HEAPU8.byteLength });
    } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        const state = message.startsWith('Unsupported:') ? 'unsupported' : message.startsWith('Limit:') ? 'limit' : 'inconclusive';
        postMessage({ id, artifact, inputDigest, state, message });
    }
};
postMessage({ ready: true, isolated: crossOriginIsolated, artifact: manifest.files['checker.wasm'],
    bundle: await hash(manifestBytes), capacity, protocols: generic ? ['portal', 'frame'] : ['portal'] });
