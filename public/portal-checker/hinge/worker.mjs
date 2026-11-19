import { compileHingeFrame } from './frame-hinge-candidate.js';
import { hingePacket } from './frame-hinge-packet.js';
import { FrameCandidates } from './frame-candidate.js';
import { captureCheckerBytes } from './frame-worker-bytes.js';

async function digest(bytes) {
    return [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))]
        .map(byte => byte.toString(16).padStart(2, '0')).join('');
}
const manifestBytes = await (await fetch(new URL('./manifest.json', import.meta.url))).arrayBuffer();
const { files } = JSON.parse(new TextDecoder().decode(manifestBytes));
let wasmBinary;
for (const [name, expected] of Object.entries(files)) {
    const response = await fetch(new URL(name, import.meta.url));
    if (!response.ok) throw Error('Missing release checker asset.');
    const bytes = await response.arrayBuffer();
    if (await digest(bytes) !== expected) throw Error('Changed release checker asset.');
    if (name === 'checker.wasm') wasmBinary = bytes;
}
if (!wasmBinary) throw Error('Missing compiled checker.');
const { default: createChecker } = await import('./checker.mjs');
const module = await createChecker({ wasmBinary });
if (module._checker_init() !== 1) throw Error('Release checker initialization failed.');
const artifact = files['checker.wasm'];
const candidates = new FrameCandidates();
self.onmessage = async ({ data }) => {
    const id = data?.id;
    let inputDigest;
    try {
        if (!Number.isSafeInteger(id) || id < 0 || data.protocol !== 'frame' || data.artifact !== artifact)
            throw Error('Invalid checker request.');
        const bytes = captureCheckerBytes(data.bytes, module._input_capacity());
        inputDigest = await digest(bytes);
        const { model, query } = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(bytes));
        const frame = compileHingeFrame(model, query);
        const packet = hingePacket(model, query, candidates.produce(frame));
        const pointer = module._input_ptr();
        module.HEAPU8.set(packet, pointer);
        const code = module._checker_check(pointer, packet.byteLength);
        if (code !== 1) {
            postMessage({ id, artifact, inputDigest, state: ['rejected', '', 'malformed', 'limit'][code] || 'inconclusive' });
            return;
        }
        postMessage({ id, artifact, inputDigest, state: 'accepted', frameProtocol: 'hinge',
            packetDigest: await digest(packet), packet });
    } catch (error) {
        const message = String(error.message ?? error);
        const state = message.startsWith('Unsupported:') ? 'unsupported' : message.startsWith('Limit:') ? 'limit' : 'inconclusive';
        postMessage({ id, artifact, inputDigest, state, message });
    }
};
postMessage({ ready: true, isolated: crossOriginIsolated, artifact, bundle: await digest(manifestBytes),
    protocols: ['frame'], capabilities: ['hinge-cardinal-v1'] });
