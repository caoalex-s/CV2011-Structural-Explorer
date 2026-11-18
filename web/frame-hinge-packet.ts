/** Canonical, bounded source/witness wire format for HingeFrame.Wire.
 * This serializer is part of the trusted drawing-to-packet boundary. It does
 * not check equilibrium. Only the source-level compiled Lean entry may do so.
 * IDs preserve UTF-16 code units as four-digit lowercase hex groups; labels
 * remain presentation metadata bound by the surrounding evidence envelope.
 */
import type { EvidenceQuery } from './model-evidence.js';
import { type FrameCertificate, frameLimits, recoverFrame } from './frame-candidate.js';
import { type Fraction, binary64, fraction, maxRationalDigits } from './frame-rational.js';

import { compileHingeFrame } from './frame-hinge-candidate.js';
export const hingePacketVersion = 'CV2011_HINGE_1';

/** Encode the source and witness, including claimed display identities.
 * Lean derives its own cuts and rejects a different display map. No candidate
 * stiffness, force or restraint mask is an authoritative packet input.
 */
export function hingePacket(input: unknown, query: EvidenceQuery, witness: FrameCertificate): Uint8Array {
    const frame = compileHingeFrame(input, query);
    const { model, released } = frame;
    const fields: string[] = [hingePacketVersion];
    const natural = (value: number, maximum: number) => {
        if (!Number.isInteger(value) || value < 0 || value > maximum) throw Error('Malformed packet count or index.');
        fields.push(String(value));
    };
    const rational = (value: Fraction) => {
        const normalized = fraction(value.n, value.d, maxRationalDigits);
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
        identifier(node.id); number(node.x); number(node.y); natural(node.joint === 'pinned' ? 1 : node.joint === 'custom' ? 2 : 0, 2);
        natural(node.referenceMember === undefined ? 0 : memberIndex(node.referenceMember) + 1, model.members.length);
        number(node.rotationStiffness ?? 0);
    }
    for (const member of model.members) {
        identifier(member.id);
        natural(model.nodes.findIndex(node => node.id === member.a), model.nodes.length - 1);
        natural(model.nodes.findIndex(node => node.id === member.b), model.nodes.length - 1);
        number(member.EA); number(member.EI);
        for (const rule of [member.connectionA, member.connectionB]) {
            if (rule && (rule.axial !== 'rigid' || rule.transverse !== 'rigid' || typeof rule.rotation === 'number'))
                throw Error('Unsupported: only rotational releases can be encoded.');
            natural(!rule ? 0 : rule.rotation === 'rigid' ? 1 : 2, 2);
        }
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
    natural(witness.points.length, frameLimits.points);
    if (witness.motion.length !== 3 * witness.points.length + released.length) throw Error('Malformed point-map dimensions.');
    for (const point of witness.points) {
        natural(point.owner === 'node' ? 0 : 1, 1);
        natural(point.index, (point.owner === 'node' ? model.nodes.length : model.members.length) - 1);
        rational(point.t); rational(point.x); rational(point.y);
    }
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
    if (!mechanism) for (const member of model.members) {
        for (const parameter of [0, 1]) {
            const face = { ...query, member: member.id, parameter, cutSide: parameter === 0 ? 'right' as const : 'left' as const };
            rational(recoverFrame({ ...frame, query: face }, witness.motion)[2]);
        }
    }
    const bytes = new TextEncoder().encode(fields.join('\n'));
    if (bytes.length > frameLimits.bytes) throw Error('Limit: checker packet exceeds 1 MiB.');
    return bytes;
}
