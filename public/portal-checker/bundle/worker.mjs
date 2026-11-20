// Inclined runtime draft: preserve captured requests and copy exact ABI reports.
const hash = async bytes => [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))]
    .map(byte => byte.toString(16).padStart(2, '0')).join('');
const manifestBytes = await (await fetch(new URL('./manifest.json', import.meta.url))).arrayBuffer();
const manifest = JSON.parse(new TextDecoder().decode(manifestBytes));
if (manifest.theorem !== 'InclinedFrameIntervalReportSound.checkReport_sound' ||
    manifest.status !== 'proved-compiled' || manifest.frameSemantics !== 'affine-vertical-v1' ||
    manifest.inclinedSemantics !== 'real-binary64-v1') throw Error('Unproved checker bundle');
const assets = {};
const codeAssets = ['checker.wasm', 'checker.mjs', 'checker.worker.js', 'checker.mjs.symbols'];
codeAssets.push('frame-rational.js', 'model-evidence.js', 'frame-candidate.js', 'frame-packet.js', 'frame-result.js',
    'frame-interval.js', 'frame-interval-geometry.js', 'frame-interval-basis.js', 'frame-interval-model.js',
    'frame-interval-solve.js', 'frame-interval-packet.js', 'frame-interval-result.js', 'frame-interval-abi.js',
    'frame-worker-bytes.js');
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
const frameCode = await import('./frame-candidate.js');
const packetCode = await import('./frame-packet.js');
const resultCode = await import('./frame-result.js');
const intervalPacketCode = await import('./frame-interval-packet.js');
const intervalResultCode = await import('./frame-interval-result.js');
const { copyInclinedReport } = await import('./frame-interval-abi.js');
const { captureCheckerBytes } = await import('./frame-worker-bytes.js');
const candidates = new frameCode.FrameCandidates();
self.onmessage = async ({ data }) => {
    let id, artifact, inputDigest;
    try {
        if (!data || typeof data !== 'object' || Array.isArray(data)) throw Error('Malformed checker request.');
        if (!Number.isSafeInteger(data.id) || data.id < 0 || typeof data.artifact !== 'string')
            throw Error('Malformed checker request identity.');
        id = data.id; artifact = data.artifact;
        if (artifact !== manifest.files['checker.wasm']) { postMessage({ id, artifact, state: 'artifact-mismatch' }); return; }
        const protocol = data.protocol;
        if (protocol !== 'frame' && protocol !== 'portal') throw Error('Malformed checker protocol.');
        // Reject malformed, shared or oversized containers before copying/hashing.
        const bytes = captureCheckerBytes(data.bytes, capacity);
        inputDigest = await hash(bytes);
        // The legacy decoder must never interpret an accepted generic packet
        // as the old fixed 21-value result, even when both share one ABI.
        if (protocol === 'portal' && (bytes[0] === undefined ||
            (bytes[0] !== 45 && (bytes[0] < 48 || bytes[0] > 57)))) throw Error('Malformed portal packet.');
        let packet = bytes;
        let inclined = false;
        if (protocol === 'frame') {
            const source = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(bytes));
            if (!source || typeof source !== 'object' || Array.isArray(source) ||
                Object.keys(source).some(key => key !== 'model' && key !== 'query') || !source.model || !source.query)
                throw Error('Malformed frame request.');
            let frame;
            try {
                inclined = data.intervalProposal === true;
                if (!inclined) frame = frameCode.compileFrame(source.model, source.query);
            }
            catch (error) {
                if (!(error instanceof Error) || !error.message.startsWith('Unsupported:')) throw error;
                inclined = true;
            }
            // Preserve the exact route whenever it supports the captured source.
            // An inclined proposal still grants nothing until the ABI accepts it.
            packet = inclined
                ? intervalPacketCode.proposeInclinedPacket(source.model, source.query, 96).packet
                : packetCode.framePacket(source.model, source.query, candidates.produce(frame));
        }
        if (packet.length > capacity) { postMessage({ id, artifact, inputDigest, state: 'limit' }); return; }
        module.HEAPU8.set(packet, pointer);
        const code = module._checker_check(pointer, packet.length);
        const states = inclined
            ? ['inconclusive', 'accepted', 'inconclusive', 'limit', 'uninitialized']
            : ['rejected', 'accepted', 'malformed', 'limit', 'uninitialized'];
        const state = states[code] ?? 'error';
        // Only the bytes accepted by this ABI call supply displayed values.
        let checked, frame, interval, report, reportDigest, packetDigest;
        if (code === 1 && protocol === 'frame') {
            if (inclined) {
                report = copyInclinedReport(module);
                interval = intervalResultCode.decodeAcceptedIntervalReport(report);
                reportDigest = await hash(report);
            } else frame = resultCode.decodeAcceptedFramePacket(packet);
            packetDigest = await hash(packet);
        } else if (code === 1) {
            const fields = new TextDecoder().decode(packet).split('\n');
            checked = Array.from({ length: 21 }, (_, i) => ({ numerator: fields[2 * i], denominator: fields[2 * i + 1] }));
        }
        postMessage({ id, artifact, inputDigest, state, checked, frame, interval, report, reportDigest, packetDigest,
            frameProtocol: protocol === 'frame' ? (inclined ? 'inclined' : 'exact') : undefined,
            packet: code === 1 && protocol === 'frame' ? packet : undefined, memoryBytes: module.HEAPU8.byteLength });
    } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        const state = message.startsWith('Unsupported:') ? 'unsupported' : message.startsWith('Limit:') ? 'limit' : 'inconclusive';
        postMessage({ id, artifact, inputDigest, state, message });
    }
};
postMessage({ ready: true, isolated: crossOriginIsolated, artifact: manifest.files['checker.wasm'],
    bundle: await hash(manifestBytes), capacity, protocols: ['portal', 'frame'],
    capabilities: ['affine-vertical-v1', 'inclined-real-v1'] });
