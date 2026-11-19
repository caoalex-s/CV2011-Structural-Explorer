/** Untrusted generic candidates for the supported axis-aligned rigid class.
 * Source ownership, exact cuts, load terms and queried values are retained in
 * the packet; neither this solver nor its cache establishes checked status.
 */
                                         
                                                         
import { parseEvidenceModel } from './model-evidence.js';
import {                zero, one, fraction, integer, binary64, encoded,
    add, sub, mul, div, neg, equal, compare, absolute, square, sum, dot } from './frame-rational.js';

export const frameLimits = Object.freeze({ members: 8, nodes: 16, points: 16, segments: 16,
    supports: 16, loads: 16, coordinates: 48, bytes: 1024 * 1024 });
export const frameQueryConvention = Object.freeze({ quantity: 'N,V,M,rotation,ux,uy',
    units: 'kN,kN,kN m,rad,m,m', signConvention: 'tension N positive; dM/dx=V; sagging M positive; global y upward; rotation CCW' });

                                                                                                              
                               
                                                                             
                                                                                                                      
                                                                                     
 
                                
                                                                                       
                                                                                   
                                                                        
 
                                   
                                                                                                    
                                                                                        
 

const matrix = (rows        , columns = rows)               =>
    Array.from({ length: rows }, () => Array          (columns).fill(zero));
const token = (value          )         => `${value.n}/${value.d}`;
const unsupported = (message        )        => { throw Error('Unsupported: ' + message); };
function within(value        , maximum        , name        )       {
    if (value > maximum) throw Error(`Limit: at most ${maximum} ${name}.`);
}

/** Validate the advertised class without silently correcting the drawing. */
export function validateFrame(input         , query               )        {
    // Reject excessive source lists before the strict parser maps or searches them.
    if (input && typeof input === 'object') {
        const outer = input                           ;
        const raw = (outer.version === 2 ? outer.model : outer)                                  ;
        if (raw && typeof raw === 'object') for (const field of ['nodes', 'members', 'supports', 'loads']         ) {
            if (Array.isArray(raw[field])) within(raw[field].length, frameLimits[field], field);
        }
    }
    const model = parseEvidenceModel(input);
    for (const items of [model.nodes, model.members, model.supports, model.loads]) {
        for (const item of items) within(item.id.length, 256, 'UTF-16 code units in an identifier');
    }
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
        const a = model.nodes.find(node => node.id === member.a) , b = model.nodes.find(node => node.id === member.b) ;
        if (a.x !== b.x && a.y !== b.y) unsupported('members must be exactly horizontal or vertical.');
        for (const connection of [member.connectionA, member.connectionB]) {
            if (connection && Object.values(connection).some(rule => rule !== 'rigid')) unsupported('member-end releases and springs are not supported.');
        }
    }
    for (const support of model.supports) {
        if (!['pin', 'fixed', 'roller'].includes(support.kind)) unsupported('use fixed, pin or axis-aligned roller supports.');
        if (support.kind === 'roller' && ![0, 90, 180, 270].includes(support.angle)) unsupported('roller angles must be exactly 0, 90, 180 or 270 degrees.');
    }
    if (!model.members.some(member => member.id === query.member) || !Number.isFinite(query.parameter) || query.parameter < 0 || query.parameter > 1)
        throw Error('Malformed query: select an existing member and a parameter in [0,1].');
    if (!['left', 'right'].includes(query.cutSide)) unsupported('select an explicit left or right cut side.');
    if ((query.parameter === 0 && query.cutSide !== 'right') || (query.parameter === 1 && query.cutSide !== 'left'))
        unsupported('endpoint queries use the interior limit: right at t=0 and left at t=1.');
    for (const field of ['quantity', 'units', 'signConvention']         ) {
        if (query[field] !== frameQueryConvention[field]) unsupported('the query units and sign convention must use the supported frame convention.');
    }
    return model;
}

/** Element coefficients use the exact local action order from LocalFrameFields. */
function elementStiffness(length          , EA          , EI          )               {
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
export function compileFrame(input         , query               )                {
    const model = validateFrame(input, query);
    const points               = model.nodes.map((node, index) => ({ owner: 'node', index, t: zero, x: binary64(node.x), y: binary64(node.y) }));
    const segments                 = [];
    const locations                        = [];
    for (const [memberIndex, member] of model.members.entries()) {
        const start = model.nodes.findIndex(node => node.id === member.a), end = model.nodes.findIndex(node => node.id === member.b);
        const dx = sub(points[end].x, points[start].x), dy = sub(points[end].y, points[start].y);
        const length = add(absolute(dx), absolute(dy));
        const c = div(dx, length), s = div(dy, length);
        const cuts = new Map                  ([[token(zero), zero], [token(one), one]]);
        const insert = (number        ) => { const value = binary64(number); cuts.set(token(value), value); };
        for (const support of model.supports) if (support.member === member.id) insert(support.t);
        for (const load of model.loads) if (load.member === member.id) {
            insert(load.t);
            if (load.kind === 'distributed') insert(load.end);
        }
        const ordered = [...cuts.values()].sort(compare), pointAt = new Map                ();
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
            const a = pointAt.get(token(from)) , b = pointAt.get(token(to)) ;
            let vertical = zero, verticalEnd = zero;
            for (const load of model.loads) {
                if (load.member === member.id && load.kind === 'distributed' &&
                    compare(binary64(load.t), from) <= 0 && compare(to, binary64(load.end)) <= 0) {
                    // Restrict each affine source load to this interval before
                    // summing overlaps. Stored fy is physical upward-positive.
                    const start = binary64(load.t), extent = sub(binary64(load.end), start);
                    const intensity = (t          ) => add(binary64(load.fy),
                        mul(sub(binary64(load.qEnd), binary64(load.fy)), div(sub(t, start), extent)));
                    vertical = add(vertical, intensity(from));
                    verticalEnd = add(verticalEnd, intensity(to));
                }
            }
            const p0 = mul(s, vertical), p1 = mul(s, verticalEnd);
            const q0 = mul(c, vertical), q1 = mul(c, verticalEnd);
            const weighted = (a          , b          , left        , right        ) =>
                add(mul(integer(left), a), mul(integer(right), b));
            const force = [
                div(mul(L, weighted(p0, p1, 2, 1)), integer(6)),
                div(mul(L, weighted(q0, q1, 7, 3)), integer(20)),
                div(mul(square(L), weighted(q0, q1, 3, 2)), integer(60)),
                div(mul(L, weighted(p0, p1, 1, 2)), integer(6)),
                div(mul(L, weighted(q0, q1, 3, 7)), integer(20)),
                neg(div(mul(square(L), weighted(q0, q1, 2, 3)), integer(60))),
            ];
            const horizontal = c.n !== 0n;
            const indices = [3 * a + (horizontal ? 0 : 1), 3 * a + (horizontal ? 1 : 0), 3 * a + 2,
                3 * b + (horizontal ? 0 : 1), 3 * b + (horizontal ? 1 : 0), 3 * b + 2];
            const signs = [horizontal ? c : s, horizontal ? c : neg(s), one,
                horizontal ? c : s, horizontal ? c : neg(s), one];
            segments.push({ member: memberIndex, start: a, end: b, from, to, length: L, c, s,
                EA: binary64(member.EA), EI: binary64(member.EI), vertical, verticalEnd, indices, signs,
                stiffness: elementStiffness(L, binary64(member.EA), binary64(member.EI)),
                force });
        }
    }
    const count = 3 * points.length;
    within(count, frameLimits.coordinates, 'motion coordinates');
    const stiffness = matrix(count), force = Array          (count).fill(zero), blocked = Array         (count).fill(false);
    for (const segment of segments) for (let i = 0; i < 6; i++) {
        const row = segment.indices[i];
        force[row] = add(force[row], mul(segment.signs[i], segment.force[i]));
        for (let j = 0; j < 6; j++) {
            const column = segment.indices[j];
            stiffness[row][column] = add(stiffness[row][column], mul(mul(segment.signs[i], segment.signs[j]), segment.stiffness[i][j]));
        }
    }
    const locate = (memberId        , t        )         => locations[model.members.findIndex(member => member.id === memberId)].get(token(binary64(t))) ;
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
function factor(matrix              )                                                       {
    const lower = matrix.map(() => Array          (matrix.length).fill(zero)), diagonal             = [];
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
function nullVector(input              )             {
    const rows = input.map(row => [...row]), pivots           = [];
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
    const vector = Array          (input.length).fill(zero);
    vector[free] = one;
    pivots.forEach((column, row) => { vector[column] = neg(rows[row][free]); });
    return vector;
}

/** Affine loaded fields, in local N,V,M,rotation then global ux,uy order. */
export function recoverFrame(frame               , motion            )             {
    const member = frame.model.members.findIndex(item => item.id === frame.query.member), t = binary64(frame.query.parameter);
    const candidates = frame.segments.filter(segment => segment.member === member && compare(segment.from, t) <= 0 && compare(t, segment.to) <= 0);
    const segment = frame.query.cutSide === 'left' ? candidates[0] : candidates[candidates.length - 1];
    if (!segment) throw Error('Malformed query: no owned segment.');
    const local = segment.indices.map((index, i) => mul(segment.signs[i], motion[index]));
    const actions = segment.stiffness.map((row, i) => sub(dot(row, local), segment.force[i]));
    const x = mul(segment.length, div(sub(t, segment.from), sub(segment.to, segment.from)));
    const x2 = square(x), x3 = mul(x2, x), x4 = square(x2);
    const p = mul(segment.s, segment.vertical), q = mul(segment.c, segment.vertical);
    const slope = div(sub(segment.verticalEnd, segment.vertical), segment.length);
    const dp = mul(segment.s, slope), dq = mul(segment.c, slope);
    const term = (coefficient          , power          , denominator        ) => div(mul(coefficient, power), integer(denominator));
    const N = sub(sub(neg(actions[0]), mul(p, x)), term(dp, x2, 2));
    const V = sum([actions[1], mul(q, x), term(dq, x2, 2)]);
    const M = sum([neg(actions[2]), mul(actions[1], x), term(q, x2, 2), term(dq, x3, 6)]);
    const u = add(local[0], div(sum([mul(neg(actions[0]), x), neg(term(p, x2, 2)), neg(term(dp, x3, 6))]), segment.EA));
    const v = sum([local[1], mul(local[2], x), div(sum([term(neg(actions[2]), x2, 2),
        term(actions[1], x3, 6), term(q, x4, 24), term(dq, mul(x4, x), 120)]), segment.EI)]);
    const rotation = add(local[2], div(sum([mul(neg(actions[2]), x), term(actions[1], x2, 2),
        term(q, x3, 6), term(dq, x4, 24)]), segment.EI));
    return [N, V, M, rotation, sub(mul(segment.c, u), mul(segment.s, v)), add(mul(segment.s, u), mul(segment.c, v))];
}

/** One-entry cache is untrusted and keyed by the entire structural boundary. */
export class FrameCandidates {
            cache                                                                    = null;
    produce(frame               )                   {
        const reduced = frame.free.map(i => frame.free.map(j => frame.stiffness[i][j]));
        let factors = this.cache?.key === frame.boundaryKey ? this.cache : factor(reduced);
        const motion = Array          (frame.force.length).fill(zero);
        if (!factors) {
            const mechanism = nullVector(reduced);
            frame.free.forEach((index, i) => { motion[index] = mechanism[i]; });
            return { kind: 'mechanism', points: frame.points, motion, reactions: [], lower: [], diagonal: [], readouts: [], loadWork: dot(frame.force, motion) };
        }
        this.cache = { key: frame.boundaryKey, ...factors };
        const { lower, diagonal } = factors;
        const intermediate             = [], reducedMotion = Array          (frame.free.length).fill(zero);
        frame.free.forEach((index, row) => {
            intermediate.push(sub(frame.force[index], sum(intermediate.map((value, column) => mul(lower[row][column], value)))));
        });
        for (let row = frame.free.length - 1; row >= 0; row--) {
            const later = sum(reducedMotion.slice(row + 1).map((value, offset) => mul(lower[row + 1 + offset][row], value)));
            reducedMotion[row] = sub(div(intermediate[row], diagonal[row]), later);
            motion[frame.free[row]] = reducedMotion[row];
        }
        const reactions = frame.stiffness.map((row, i) => sub(dot(row, motion), frame.force[i]));
        return { kind: 'solution', points: frame.points, motion, reactions, lower, diagonal, readouts: recoverFrame(frame, motion), loadWork: zero };
    }
}

/** Expose exact values for diagnostics; this is explicitly an untrusted proposal. */
export function candidateValues(certificate                  ) {
    return { kind: certificate.kind, motion: certificate.motion.map(encoded), reactions: certificate.reactions.map(encoded),
        lower: certificate.lower.map(row => row.map(encoded)), diagonal: certificate.diagonal.map(encoded),
        readouts: certificate.readouts.map(encoded), loadWork: encoded(certificate.loadWork) };
}
