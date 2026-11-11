/** Canonical, bounded source/witness wire format for RationalFrameWire.
 * This serializer is part of the trusted drawing-to-packet boundary. It does
 * not check equilibrium. Only the source-level compiled Lean entry may do so.
 * IDs preserve UTF-16 code units as four-digit lowercase hex groups; labels
 * remain presentation metadata bound by the surrounding evidence envelope.
 */
import type { EvidenceQuery } from './model-evidence.js';
import { type FrameCertificate, frameLimits, validateFrame } from './frame-candidate.js';
import { type Fraction, binary64, fraction } from './frame-rational.js';

export const framePacketVersion = 'CV2011_FRAME_1';

/** Encode the source itself; never serialize candidate cuts, K, F or a mask. */
export function framePacket(input: unknown, query: EvidenceQuery, witness: FrameCertificate): Uint8Array {
    const model = validateFrame(input, query);
    const fields: string[] = [framePacketVersion];
    const natural = (value: number, maximum: number) => {
        if (!Number.isInteger(value) || value < 0 || value > maximum) throw Error('Malformed packet count or index.');
        fields.push(String(value));
    };
    const rational = (value: Fraction) => {
        const normalized = fraction(value.n, value.d);
        fields.push(String(normalized.n), String(normalized.d));
    };
    const number = (value: number) => rational(binary64(value));
    const identifier = (value: string) => {
        let encoded = '';
        for (let i = 0; i < value.length; i++) encoded += value.charCodeAt(i).toString(16).padStart(4, '0');
        fields.push(encoded);
    };
    const memberIndex = (id: string) => model.members.findIndex(member => member.id === id);
    natural(model.nodes.length, frameLimits.nodes);
    natural(model.members.length, frameLimits.members);
    natural(model.supports.length, frameLimits.supports);
    natural(model.loads.length, frameLimits.loads);
    for (const node of model.nodes) {
        identifier(node.id); number(node.x); number(node.y); natural(0, 0);
        natural(node.referenceMember === undefined ? 0 : memberIndex(node.referenceMember) + 1, model.members.length);
        number(node.rotationStiffness ?? 0);
    }
    for (const member of model.members) {
        identifier(member.id);
        natural(model.nodes.findIndex(node => node.id === member.a), model.nodes.length - 1);
        natural(model.nodes.findIndex(node => node.id === member.b), model.nodes.length - 1);
        number(member.EA); number(member.EI); natural(1, 1);
    }
    for (const support of model.supports) {
        identifier(support.id); natural(memberIndex(support.member), model.members.length - 1); number(support.t);
        natural(support.kind === 'pin' ? 0 : support.kind === 'fixed' ? 1 : 2, 2); number(support.angle);
    }
    for (const load of model.loads) {
        identifier(load.id); natural(memberIndex(load.member), model.members.length - 1);
        natural(load.kind === 'force' ? 0 : load.kind === 'moment' ? 1 : 2, 2);
        for (const value of [load.t, load.end, load.fx, load.fy, load.mz, load.qEnd]) number(value);
    }
    natural(memberIndex(query.member), model.members.length - 1); number(query.parameter);
    natural(query.cutSide === 'right' ? 1 : 0, 1); natural(1, 1);
    const mechanism = witness.kind === 'mechanism';
    natural(mechanism ? 1 : 0, 1);
    natural(witness.motion.length, frameLimits.coordinates);
    natural(witness.diagonal.length, frameLimits.coordinates);
    witness.motion.forEach(rational);
    if (mechanism) {
        if (witness.reactions.length || witness.lower.length || witness.diagonal.length || witness.readouts.length)
            throw Error('Malformed mechanism witness: unexpected solution fields.');
    } else {
        const size = witness.diagonal.length;
        if (witness.reactions.length !== witness.motion.length || witness.lower.length !== size ||
            witness.lower.some(row => row.length !== size) || witness.readouts.length !== 6)
            throw Error('Malformed solution witness dimensions.');
        witness.reactions.forEach(rational);
        witness.lower.forEach(row => row.forEach(rational));
        witness.diagonal.forEach(rational);
        witness.readouts.forEach(rational);
    }
    rational(witness.loadWork);
    const bytes = new TextEncoder().encode(fields.join('\n'));
    if (bytes.length > frameLimits.bytes) throw Error('Limit: checker packet exceeds 1 MiB.');
    return bytes;
}
