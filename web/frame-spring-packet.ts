/** Compact untrusted proposals for FrameSpring.Wire.
 * Original binary64 source values retain their exact rational interpretation.
 * Lean reconstructs every interval table and output; this module grants no status.
 */
import type { EvidenceQuery } from './model-evidence.js';
import { endConnection, type Model } from './engine.js';
import { parseEvidenceModel } from './model-evidence.js';
import { frameLimits } from './frame-candidate.js';
import { type Fraction, binary64, fraction, maxRationalDigits, sub } from './frame-rational.js';
import { IntervalArithmetic } from './frame-interval.js';
import { memberGeometry } from './frame-interval-geometry.js';
import { compileInclinedRelease } from './frame-inclined-release.js';
import { proposeIntervalSolution } from './frame-interval-solve.js';

export const springPacketVersion = 'CV2011_ROTATIONAL_SPRING_1';

/** Produce source/query plus root brackets, inverse and displacement estimates.
 * Exhausted numerical or packet budgets are inconclusive, never a mechanism.
 * No producer-computed matrix, support mask, q/eta or readout is serialized.
 */
export function proposeSpringPacket(input: unknown, query: EvidenceQuery, bits: number) {
    const arithmetic = new IntervalArithmetic(bits);
    const model = parseEvidenceModel(input);
    for (const key of ['nodes', 'members', 'loads', 'supports'] as const) {
        if (model[key].length > frameLimits[key]) throw Error(`Limit: too many ${key}.`);
    }
    // Retain each spring rotation as a separate coordinate. The free-end
    // layout supplies the beam contribution, then each spring adds k b bᵀ.
    const kinematicModel: Model = { ...model,
        nodes: model.nodes.map(node => ({ ...node, joint: 'custom' })),
        members: model.members.map(member => ({ ...member })) };
    const springs: { endPoint: number; referencePoint: number; stiffness: number }[] = [];
    let nextPoint = model.nodes.length;
    for (const [index, member] of model.members.entries()) {
        for (const end of ['a', 'b'] as const) {
            const rule = endConnection(model, member, end);
            if (rule.axial !== 'rigid' || rule.transverse !== 'rigid')
                throw Error('Unsupported: this checker requires shared joint translations.');
            const property = end === 'a' ? 'connectionA' : 'connectionB';
            kinematicModel.members[index][property] = { ...rule, rotation: rule.rotation === 'rigid' ? 'rigid' : 'free' };
            if (rule.rotation === 'rigid') continue;
            if (typeof rule.rotation === 'number') {
                if (!Number.isFinite(rule.rotation) || rule.rotation <= 0) throw Error('Invalid rotational stiffness.');
                springs.push({ endPoint: nextPoint, referencePoint: model.nodes.findIndex(node => node.id === member[end]), stiffness: rule.rotation });
            }
            nextPoint++;
        }
    }
    if (!springs.length) throw Error('Unsupported: draw at least one rotational spring.');
    const frame = compileInclinedRelease(arithmetic, kinematicModel, query);
    for (const spring of springs) {
        const k = arithmetic.bounds(binary64(spring.stiffness));
        const rotations = frame.coordinates.map(column => !column.rotation ? 0 :
            column.point === spring.endPoint ? 1 : column.point === spring.referencePoint ? -1 : 0);
        for (const [i, row] of rotations.entries()) for (const [j, col] of rotations.entries()) {
            if (row && col) frame.reduced[i][j] = row === col ? arithmetic.add(frame.reduced[i][j], k) :
                arithmetic.subtract(frame.reduced[i][j], k);
        }
    }
    const solution = proposeIntervalSolution(arithmetic, frame.reduced, frame.reducedForce);
    const fields: string[] = [springPacketVersion];
    const natural = (value: number, maximum: number) => {
        if (!Number.isInteger(value) || value < 0 || value > maximum)
            throw Error('Malformed inclined packet count or index.');
        fields.push(String(value));
    };
    const rational = (value: Fraction) => {
        const normalized = fraction(value.n, value.d, maxRationalDigits);
        fields.push(String(normalized.n), String(normalized.d));
    };
    const number = (value: number) => rational(binary64(value));
    const identifier = (value: string) => {
        let encoded = '';
        for (let index = 0; index < value.length; index++)
            encoded += value.charCodeAt(index).toString(16).padStart(4, '0');
        fields.push(encoded);
    };
    const memberIndex = (id: string) => model.members.findIndex(member => member.id === id);

    // 1. Preserve the established canonical source field order and identifiers.
    natural(model.nodes.length, frameLimits.nodes);
    natural(model.members.length, frameLimits.members);
    natural(model.supports.length, frameLimits.supports);
    natural(model.loads.length, frameLimits.loads);
    for (const node of model.nodes) {
        identifier(node.id);
        number(node.x); number(node.y); natural(node.joint === 'semi-rigid' ? 3 : node.joint === 'pinned' ? 1 : node.joint === 'custom' ? 2 : 0, 3);
        natural(node.referenceMember === undefined ? 0 : memberIndex(node.referenceMember) + 1, model.members.length);
        number(node.rotationStiffness ?? (node.joint === 'semi-rigid' ? 20000 : 0));
    }
    for (const member of model.members) {
        identifier(member.id);
        natural(model.nodes.findIndex(node => node.id === member.a), model.nodes.length - 1);
        natural(model.nodes.findIndex(node => node.id === member.b), model.nodes.length - 1);
        number(member.EA); number(member.EI);
        for (const end of [member.connectionA, member.connectionB]) {
            natural(!end ? 0 : end.rotation === 'rigid' ? 1 : end.rotation === 'free' ? 2 : 3, 3);
            number(typeof end?.rotation === 'number' ? end.rotation : 0);
        }
    }
    for (const support of model.supports) {
        identifier(support.id);
        natural(memberIndex(support.member), model.members.length - 1);
        number(support.t);
        natural(support.kind === 'pin' ? 0 : support.kind === 'fixed' ? 1 : 2, 2);
        number(support.angle);
    }
    for (const load of model.loads) {
        identifier(load.id);
        natural(memberIndex(load.member), model.members.length - 1);
        natural(load.kind === 'force' ? 0 : load.kind === 'moment' ? 1 : 2, 2);
        for (const value of [load.t, load.end, load.fx, load.fy, load.mz, load.qEnd]) number(value);
    }
    natural(memberIndex(query.member), model.members.length - 1);
    number(query.parameter);
    natural(query.cutSide === 'right' ? 1 : 0, 1);
    natural(1, 1);
    natural(bits, 128);

    // 2. Root brackets use whole original members, not source-cut lengths.
    for (const member of model.members) {
        const start = model.nodes.find(node => node.id === member.a)!;
        const finish = model.nodes.find(node => node.id === member.b)!;
        const root = memberGeometry(arithmetic,
            sub(binary64(finish.x), binary64(start.x)),
            sub(binary64(finish.y), binary64(start.y))).length;
        rational(root.lower);
        rational(root.upper);
    }
    // Dimensions are implicit: Lean derives them from its own source basis.
    for (const row of solution.inverse) for (const entry of row) rational(entry);
    for (const entry of solution.estimate) rational(entry);
    if (fields.length > 6000) throw Error('Limit: inclined checker packet exceeds 6000 fields.');
    const packet = new TextEncoder().encode(fields.join('\n'));
    if (packet.length > frameLimits.bytes) throw Error('Limit: inclined checker packet exceeds 1 MiB.');
    return { packet, precisionBits: bits, coordinates: frame.coordinates.length };
}
