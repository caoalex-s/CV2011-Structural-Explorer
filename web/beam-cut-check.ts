import { frameQueryConvention } from './frame-candidate.js';
import { decodeAcceptedFramePacket } from './frame-result.js';
import { PortalRuntime, sha256 } from './portal-runtime.js';
import { beamValues, lessonBeam, type BeamInputs, type CutSide } from './lesson-beam.js';
import type { Rational } from './portal-candidate.js';

let runtime: PortalRuntime | undefined;
let revision = 0;
export function invalidateBeamCheck() { revision++; runtime?.invalidate(); }

export async function checkBeam(inputs: BeamInputs, parameter: number, cutSide: CutSide) {
    const current = revision;
    const query = { member: 'AB', parameter, cutSide, ...frameQueryConvention };
    const sourceRequest = { model: lessonBeam(inputs), query };
    const bytes = new TextEncoder().encode(JSON.stringify(sourceRequest));
    if (!runtime || runtime.needsReset) runtime = new PortalRuntime(new URL('./portal-checker/bundle/worker.mjs', location.href));
    await runtime.ready;
    if (current !== revision) return;
    const result = await runtime.checkFrame(bytes);
    if (current !== revision) return;
    if (result.state !== 'accepted' || !(result.packet instanceof Uint8Array) ||
        result.inputDigest !== await sha256(bytes) || result.packetDigest !== await sha256(result.packet))
        throw Error('The checker could not verify this cut (' + result.state + ').');
    const frame = decodeAcceptedFramePacket(result.packet);
    // The station and the equilibrium results are multiples of 1/32 on this grid.
    const matches = (actual: Rational | undefined, expected: number) =>
        !!actual && BigInt(actual.numerator) * 32n === BigInt(expected * 32) * BigInt(actual.denominator);
    const expected = beamValues(inputs, parameter, cutSide);
    const reaction = (id: string) => frame.points.find(p => p.owner === 'node' && p.id === id)?.reaction?.[1];
    if (frame.kind !== 'solution' || frame.query.member !== query.member || frame.query.cutSide !== cutSide ||
        !matches(frame.query.parameter, parameter) || !matches(reaction('A'), expected.left) || !matches(reaction('B'), expected.right) ||
        ![0, expected.shear, expected.moment].every((value, index) => matches(frame.readouts[index], value)))
        throw Error('The checked frame result and section equilibrium disagree.');
    return { sourceRequest, inputDigest: result.inputDigest, packetDigest: result.packetDigest,
        packet: new TextDecoder().decode(result.packet), artifact: runtime.artifact,
        values: { normal: 0, shear: expected.shear, moment: expected.moment, Ay: expected.left, By: expected.right } };
}
