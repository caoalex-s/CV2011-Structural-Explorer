/** Compact untrusted proposals for InclinedFrameIntervalWire.
 * Original binary64 source values retain their exact rational interpretation.
 * Lean reconstructs every interval table and output; this module grants no status.
 */
                                                         
import { frameLimits } from './frame-candidate.js';
import {                binary64, fraction, maxRationalDigits, sub } from './frame-rational.js';
import { IntervalArithmetic } from './frame-interval.js';
import { memberGeometry } from './frame-interval-geometry.js';
import { compileInclinedRelease } from './frame-inclined-release.js';
import { proposeIntervalSolution } from './frame-interval-solve.js';

export const inclinedReleasePacketVersion = 'CV2011_INCLINED_RELEASE_1';

/** Produce source/query plus root brackets, inverse and displacement estimates.
 * Exhausted numerical or packet budgets are inconclusive, never a mechanism.
 * No producer-computed matrix, support mask, q/eta or readout is serialized.
 */
export function proposeInclinedReleasePacket(input         , query               , bits        ) {
    const arithmetic = new IntervalArithmetic(bits);
    const frame = compileInclinedRelease(arithmetic, input, query);
    const model = frame.model;
    const solution = proposeIntervalSolution(arithmetic, frame.reduced, frame.reducedForce);
    const fields           = [inclinedReleasePacketVersion];
    const natural = (value        , maximum        ) => {
        if (!Number.isInteger(value) || value < 0 || value > maximum)
            throw Error('Malformed inclined packet count or index.');
        fields.push(String(value));
    };
    const rational = (value          ) => {
        const normalized = fraction(value.n, value.d, maxRationalDigits);
        fields.push(String(normalized.n), String(normalized.d));
    };
    const number = (value        ) => rational(binary64(value));
    const identifier = (value        ) => {
        let encoded = '';
        for (let index = 0; index < value.length; index++)
            encoded += value.charCodeAt(index).toString(16).padStart(4, '0');
        fields.push(encoded);
    };
    const memberIndex = (id        ) => model.members.findIndex(member => member.id === id);

    // 1. Preserve the established canonical source field order and identifiers.
    natural(model.nodes.length, frameLimits.nodes);
    natural(model.members.length, frameLimits.members);
    natural(model.supports.length, frameLimits.supports);
    natural(model.loads.length, frameLimits.loads);
    for (const node of model.nodes) {
        identifier(node.id);
        number(node.x); number(node.y); natural(node.joint === 'pinned' ? 1 : node.joint === 'custom' ? 2 : 0, 2);
        natural(node.referenceMember === undefined ? 0 : memberIndex(node.referenceMember) + 1, model.members.length);
        number(node.rotationStiffness ?? 0);
    }
    for (const member of model.members) {
        identifier(member.id);
        natural(model.nodes.findIndex(node => node.id === member.a), model.nodes.length - 1);
        natural(model.nodes.findIndex(node => node.id === member.b), model.nodes.length - 1);
        number(member.EA); number(member.EI);
        for (const end of [member.connectionA, member.connectionB]) natural(!end ? 0 : end.rotation === 'rigid' ? 1 : 2, 2);
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
        const start = model.nodes.find(node => node.id === member.a) ;
        const finish = model.nodes.find(node => node.id === member.b) ;
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
