/** Untrusted generic candidates for the supported axis-aligned rigid class.
 * Source ownership, exact cuts, load terms and queried values are retained in
 * the packet; neither this solver nor its cache establishes checked status.
 */
import type { Model } from './engine.js';
import type { EvidenceQuery } from './model-evidence.js';
import { parseEvidenceModel } from './model-evidence.js';
import { type Fraction, zero, one, fraction, integer, binary64, encoded,
    add, sub, mul, div, neg, equal, compare, absolute, square, sum, dot } from './frame-rational.js';

export const frameLimits = Object.freeze({ members: 8, nodes: 16, points: 16, segments: 16,
    supports: 16, loads: 16, coordinates: 48, bytes: 1024 * 1024 });
export const frameQueryConvention = Object.freeze({ quantity: 'N,V,M,rotation,ux,uy',
    units: 'kN,kN,kN m,rad,m,m', signConvention: 'tension N positive; dM/dx=V; sagging M positive; global y upward; rotation CCW' });

export interface FramePoint { owner: 'node' | 'member'; index: number; t: Fraction; x: Fraction; y: Fraction }
export interface FrameSegment {
    member: number; start: number; end: number; from: Fraction; to: Fraction;
    length: Fraction; c: Fraction; s: Fraction; EA: Fraction; EI: Fraction; vertical: Fraction;
    indices: number[]; signs: Fraction[]; stiffness: Fraction[][]; force: Fraction[];
}
export interface CompiledFrame {
    model: Model; query: EvidenceQuery; points: FramePoint[]; segments: FrameSegment[];
    stiffness: Fraction[][]; force: Fraction[]; blocked: boolean[]; free: number[];
    supportPoints: number[]; structuralKey: string; boundaryKey: string;
}
export interface FrameCertificate {
    kind: 'solution' | 'mechanism'; motion: Fraction[]; reactions: Fraction[];
    lower: Fraction[][]; diagonal: Fraction[]; readouts: Fraction[]; loadWork: Fraction;
}

const matrix = (rows: number, columns = rows): Fraction[][] =>
    Array.from({ length: rows }, () => Array<Fraction>(columns).fill(zero));
const token = (value: Fraction): string => `${value.n}/${value.d}`;
const unsupported = (message: string): never => { throw Error('Unsupported: ' + message); };
function within(value: number, maximum: number, name: string): void {
    if (value > maximum) throw Error(`Limit: at most ${maximum} ${name}.`);
}

/** Validate the advertised class without silently correcting the drawing. */
export function validateFrame(input: unknown, query: EvidenceQuery): Model {
    const model = parseEvidenceModel(input);
    within(model.nodes.length, frameLimits.nodes, 'original nodes');
    within(model.members.length, frameLimits.members, 'members');
    within(model.supports.length, frameLimits.supports, 'supports');
    within(model.loads.length, frameLimits.loads, 'loads');
    if (!model.members.length) unsupported('draw at least one member.');
    for (const node of model.nodes) {
        if (node.joint !== 'rigid') unsupported('only rigid joints are supported.');
        if (!model.members.some(member => member.a === node.id || member.b === node.id)) unsupported('isolated nodes are not represented.');
    }
    for (const member of model.members) {
        const a = model.nodes.find(node => node.id === member.a)!, b = model.nodes.find(node => node.id === member.b)!;
        if (a.x !== b.x && a.y !== b.y) unsupported('members must be exactly horizontal or vertical.');
        for (const connection of [member.connectionA, member.connectionB]) {
            if (connection && Object.values(connection).some(rule => rule !== 'rigid')) unsupported('member-end releases and springs are not supported.');
        }
    }
    for (const support of model.supports) {
        if (!['pin', 'fixed', 'roller'].includes(support.kind)) unsupported('use fixed, pin or axis-aligned roller supports.');
        if (support.kind === 'roller' && ![0, 90, 180, 270].includes(support.angle)) unsupported('roller angles must be exactly 0, 90, 180 or 270 degrees.');
    }
    for (const load of model.loads) {
        if (load.kind === 'distributed' && load.fy !== load.qEnd) unsupported('distributed loads must be uniform.');
    }
    if (!model.members.some(member => member.id === query.member) || !Number.isFinite(query.parameter) || query.parameter < 0 || query.parameter > 1)
        throw Error('Malformed query: select an existing member and a parameter in [0,1].');
    if (!['left', 'right'].includes(query.cutSide)) unsupported('select an explicit left or right cut side.');
    if ((query.parameter === 0 && query.cutSide !== 'right') || (query.parameter === 1 && query.cutSide !== 'left'))
        unsupported('endpoint queries use the interior limit: right at t=0 and left at t=1.');
    for (const field of ['quantity', 'units', 'signConvention'] as const) {
        if (query[field] !== frameQueryConvention[field]) unsupported('the query units and sign convention must use the supported frame convention.');
    }
    return model;
}

/** Element coefficients use the exact local action order from LocalFrameFields. */
function elementStiffness(length: Fraction, EA: Fraction, EI: Fraction): Fraction[][] {
    const axial = div(EA, length), bend = div(mul(integer(12), EI), mul(square(length), length));
    const coupling = div(mul(integer(6), EI), square(length));
    const rotation = div(mul(integer(4), EI), length), halfRotation = div(rotation, integer(2));
    return [
        [axial, zero, zero, neg(axial), zero, zero],
        [zero, bend, coupling, zero, neg(bend), coupling],
        [zero, coupling, rotation, zero, neg(coupling), halfRotation],
        [neg(axial), zero, zero, axial, zero, zero],
        [zero, neg(bend), neg(coupling), zero, bend, neg(coupling)],
        [zero, coupling, halfRotation, zero, neg(coupling), rotation],
    ];
}

/** Build exact owned cuts and assembly. Query positions do not alter the mesh. */
export function compileFrame(input: unknown, query: EvidenceQuery): CompiledFrame {
    const model = validateFrame(input, query);
    const points: FramePoint[] = model.nodes.map((node, index) => ({ owner: 'node', index, t: zero, x: binary64(node.x), y: binary64(node.y) }));
    const segments: FrameSegment[] = [];
    const locations: Map<string, number>[] = [];
    for (const [memberIndex, member] of model.members.entries()) {
        const start = model.nodes.findIndex(node => node.id === member.a), end = model.nodes.findIndex(node => node.id === member.b);
        const dx = sub(points[end].x, points[start].x), dy = sub(points[end].y, points[start].y);
        const length = add(absolute(dx), absolute(dy));
        const c = div(dx, length), s = div(dy, length);
        const cuts = new Map<string, Fraction>([[token(zero), zero], [token(one), one]]);
        const insert = (number: number) => { const value = binary64(number); cuts.set(token(value), value); };
        for (const support of model.supports) if (support.member === member.id) insert(support.t);
        for (const load of model.loads) if (load.member === member.id) {
            insert(load.t);
            if (load.kind === 'distributed') insert(load.end);
        }
        const ordered = [...cuts.values()].sort(compare), pointAt = new Map<string, number>();
        for (const t of ordered) {
            let index = equal(t, zero) ? start : equal(t, one) ? end : points.length;
            if (!equal(t, zero) && !equal(t, one)) {
                within(points.length + 1, frameLimits.points, 'active points');
                points.push({ owner: 'member', index: memberIndex, t, x: add(points[start].x, mul(t, dx)), y: add(points[start].y, mul(t, dy)) });
            }
            pointAt.set(token(t), index);
        }
        locations.push(pointAt);
        for (let interval = 0; interval + 1 < ordered.length; interval++) {
            within(segments.length + 1, frameLimits.segments, 'segments');
            const from = ordered[interval], to = ordered[interval + 1], L = mul(length, sub(to, from));
            const a = pointAt.get(token(from))!, b = pointAt.get(token(to))!;
            let vertical = zero;
            for (const load of model.loads) {
                if (load.member === member.id && load.kind === 'distributed' &&
                    compare(binary64(load.t), from) <= 0 && compare(to, binary64(load.end)) <= 0) vertical = add(vertical, binary64(load.fy));
            }
            const p = mul(s, vertical), q = mul(c, vertical);
            const axial = div(mul(p, L), integer(2)), transverse = div(mul(q, L), integer(2));
            const moment = div(mul(q, square(L)), integer(12));
            const horizontal = c.n !== 0n;
            const indices = [3 * a + (horizontal ? 0 : 1), 3 * a + (horizontal ? 1 : 0), 3 * a + 2,
                3 * b + (horizontal ? 0 : 1), 3 * b + (horizontal ? 1 : 0), 3 * b + 2];
            const signs = [horizontal ? c : s, horizontal ? c : neg(s), one,
                horizontal ? c : s, horizontal ? c : neg(s), one];
            segments.push({ member: memberIndex, start: a, end: b, from, to, length: L, c, s,
                EA: binary64(member.EA), EI: binary64(member.EI), vertical, indices, signs,
                stiffness: elementStiffness(L, binary64(member.EA), binary64(member.EI)),
                force: [axial, transverse, moment, axial, transverse, neg(moment)] });
        }
    }
    const count = 3 * points.length;
    within(count, frameLimits.coordinates, 'motion coordinates');
    const stiffness = matrix(count), force = Array<Fraction>(count).fill(zero), blocked = Array<boolean>(count).fill(false);
    for (const segment of segments) for (let i = 0; i < 6; i++) {
        const row = segment.indices[i];
        force[row] = add(force[row], mul(segment.signs[i], segment.force[i]));
        for (let j = 0; j < 6; j++) {
            const column = segment.indices[j];
            stiffness[row][column] = add(stiffness[row][column], mul(mul(segment.signs[i], segment.signs[j]), segment.stiffness[i][j]));
        }
    }
    const locate = (memberId: string, t: number): number => locations[model.members.findIndex(member => member.id === memberId)].get(token(binary64(t)))!;
    for (const load of model.loads) if (load.kind !== 'distributed') {
        const point = locate(load.member, load.t);
        const action = load.kind === 'force' ? [binary64(load.fx), binary64(load.fy), zero] : [zero, zero, binary64(load.mz)];
        for (let direction = 0; direction < 3; direction++) force[3 * point + direction] = add(force[3 * point + direction], action[direction]);
    }
    const supportPoints = model.supports.map(support => locate(support.member, support.t));
    model.supports.forEach((support, i) => {
        const point = supportPoints[i];
        const directions = support.kind === 'fixed' ? [0, 1, 2] : support.kind === 'pin' ? [0, 1] : [support.angle % 180 === 0 ? 0 : 1];
        for (const direction of directions) blocked[3 * point + direction] = true;
    });
    const free = blocked.flatMap((value, index) => value ? [] : [index]);
    const structuralKey = JSON.stringify({ nodes: model.nodes, members: model.members,
        points: points.map(point => [point.owner, point.index, token(point.t), token(point.x), token(point.y)]),
        segments: segments.map(segment => [segment.member, segment.start, segment.end, token(segment.from), token(segment.to), token(segment.length)]) });
    const boundaryKey = JSON.stringify([structuralKey, model.supports, blocked]);
    return { model, query: { ...query }, points, segments, stiffness, force, blocked, free, supportPoints, structuralKey, boundaryKey };
}

/** Factor the exact reduced matrix. A zero pivot requests a null witness. */
function factor(matrix: Fraction[][]): { lower: Fraction[][]; diagonal: Fraction[] } | null {
    const lower = matrix.map(() => Array<Fraction>(matrix.length).fill(zero)), diagonal: Fraction[] = [];
    for (let i = 0; i < matrix.length; i++) {
        lower[i][i] = one;
        const pivot = sub(matrix[i][i], sum(diagonal.map((value, k) => mul(square(lower[i][k]), value))));
        if (pivot.n === 0n) return null;
        if (pivot.n < 0n) throw Error('Inconclusive: the candidate factor has a nonpositive pivot.');
        diagonal.push(pivot);
        for (let row = i + 1; row < matrix.length; row++) {
            const product = sum(diagonal.slice(0, i).map((value, k) => mul(mul(lower[row][k], lower[i][k]), value)));
            lower[row][i] = div(sub(matrix[row][i], product), pivot);
        }
    }
    return { lower, diagonal };
}

/** Exact row elimination supplies one candidate null vector, not a verdict. */
function nullVector(input: Fraction[][]): Fraction[] {
    const rows = input.map(row => [...row]), pivots: number[] = [];
    for (let column = 0; column < rows.length && pivots.length < rows.length; column++) {
        const pivotRow = rows.findIndex((row, index) => index >= pivots.length && row[column].n !== 0n);
        if (pivotRow < 0) continue;
        const current = pivots.length;
        [rows[current], rows[pivotRow]] = [rows[pivotRow], rows[current]];
        const pivot = rows[current][column];
        rows[current] = rows[current].map(value => div(value, pivot));
        for (let row = 0; row < rows.length; row++) if (row !== current) {
            const multiplier = rows[row][column];
            rows[row] = rows[row].map((value, j) => sub(value, mul(multiplier, rows[current][j])));
        }
        pivots.push(column);
    }
    const free = input.findIndex((_, index) => !pivots.includes(index));
    if (free < 0) throw Error('Inconclusive: no exact mechanism candidate was found.');
    const vector = Array<Fraction>(input.length).fill(zero);
    vector[free] = one;
    pivots.forEach((column, row) => { vector[column] = neg(rows[row][free]); });
    return vector;
}

/** Actual uniform-load fields, in local N,V,M,rotation then global ux,uy order. */
export function recoverFrame(frame: CompiledFrame, motion: Fraction[]): Fraction[] {
    const member = frame.model.members.findIndex(item => item.id === frame.query.member), t = binary64(frame.query.parameter);
    const candidates = frame.segments.filter(segment => segment.member === member && compare(segment.from, t) <= 0 && compare(t, segment.to) <= 0);
    const segment = frame.query.cutSide === 'left' ? candidates[0] : candidates[candidates.length - 1];
    if (!segment) throw Error('Malformed query: no owned segment.');
    const local = segment.indices.map((index, i) => mul(segment.signs[i], motion[index]));
    const actions = segment.stiffness.map((row, i) => sub(dot(row, local), segment.force[i]));
    const x = mul(segment.length, div(sub(t, segment.from), sub(segment.to, segment.from)));
    const x2 = square(x), x3 = mul(x2, x), x4 = square(x2);
    const p = mul(segment.s, segment.vertical), q = mul(segment.c, segment.vertical);
    const N = sub(neg(actions[0]), mul(p, x));
    const V = add(actions[1], mul(q, x));
    const M = add(add(neg(actions[2]), mul(actions[1], x)), div(mul(q, x2), integer(2)));
    const u = add(local[0], div(sub(mul(neg(actions[0]), x), div(mul(p, x2), integer(2))), segment.EA));
    const v = add(add(local[1], mul(local[2], x)), div(add(add(div(mul(neg(actions[2]), x2), integer(2)), div(mul(actions[1], x3), integer(6))), div(mul(q, x4), integer(24))), segment.EI));
    const rotation = add(local[2], div(add(add(mul(neg(actions[2]), x), div(mul(actions[1], x2), integer(2))), div(mul(q, x3), integer(6))), segment.EI));
    return [N, V, M, rotation, sub(mul(segment.c, u), mul(segment.s, v)), add(mul(segment.s, u), mul(segment.c, v))];
}

/** One-entry cache is untrusted and keyed by the entire structural boundary. */
export class FrameCandidates {
    private cache: { key: string; lower: Fraction[][]; diagonal: Fraction[] } | null = null;
    produce(frame: CompiledFrame): FrameCertificate {
        const reduced = frame.free.map(i => frame.free.map(j => frame.stiffness[i][j]));
        let factors = this.cache?.key === frame.boundaryKey ? this.cache : factor(reduced);
        const motion = Array<Fraction>(frame.force.length).fill(zero);
        if (!factors) {
            const mechanism = nullVector(reduced);
            frame.free.forEach((index, i) => { motion[index] = mechanism[i]; });
            return { kind: 'mechanism', motion, reactions: [], lower: [], diagonal: [], readouts: [], loadWork: dot(frame.force, motion) };
        }
        this.cache = { key: frame.boundaryKey, ...factors };
        const { lower, diagonal } = factors;
        const intermediate: Fraction[] = [], reducedMotion = Array<Fraction>(frame.free.length).fill(zero);
        frame.free.forEach((index, row) => {
            intermediate.push(sub(frame.force[index], sum(intermediate.map((value, column) => mul(lower[row][column], value)))));
        });
        for (let row = frame.free.length - 1; row >= 0; row--) {
            const later = sum(reducedMotion.slice(row + 1).map((value, offset) => mul(lower[row + 1 + offset][row], value)));
            reducedMotion[row] = sub(div(intermediate[row], diagonal[row]), later);
            motion[frame.free[row]] = reducedMotion[row];
        }
        const reactions = frame.stiffness.map((row, i) => sub(dot(row, motion), frame.force[i]));
        return { kind: 'solution', motion, reactions, lower, diagonal, readouts: recoverFrame(frame, motion), loadWork: zero };
    }
}

/** Expose exact values for diagnostics; this is explicitly an untrusted proposal. */
export function candidateValues(certificate: FrameCertificate) {
    return { kind: certificate.kind, motion: certificate.motion.map(encoded), reactions: certificate.reactions.map(encoded),
        lower: certificate.lower.map(row => row.map(encoded)), diagonal: certificate.diagonal.map(encoded),
        readouts: certificate.readouts.map(encoded), loadWork: encoded(certificate.loadWork) };
}
