/** Untrusted source-derived interval assembly for rigid inclined frames.
 * Geometry, cuts and support ownership come from the original drawing. This
 * proposal remains separate from the unchanged exact-cardinal checker path. */
import { parseEvidenceModel, type EvidenceQuery } from './model-evidence.js';
import { frameLimits, frameQueryConvention, type FramePoint } from './frame-candidate.js';
import { type Fraction, zero, one, integer, binary64, add, sub, mul, div, equal, compare } from './frame-rational.js';
import { IntervalArithmetic, type RationalInterval } from './frame-interval.js';
import { memberGeometry } from './frame-interval-geometry.js';
import { pointBasis } from './frame-interval-basis.js';
import { intervalDot, type IntervalMatrix } from './frame-interval-solve.js';

const key = (value: Fraction) => `${value.n}/${value.d}`;
export interface EnclosedSegment {
    member: number;
    start: number;
    end: number;
    from: Fraction;
    to: Fraction;
    length: RationalInterval;
    cosine: RationalInterval;
    sine: RationalInterval;
    vertical: Fraction;
    verticalEnd: Fraction;
    EA: Fraction;
    EI: Fraction;
    /** Local order: axial displacement, transverse displacement, rotation at each end. */
    localStiffness: IntervalMatrix;
    localForce: RationalInterval[];
    transform: IntervalMatrix;
}

/** Assemble PᵀKP and PᵀF from owned source cuts and all support constraints.
 * Throws on unsupported source features or exhausted arithmetic/size budgets.
 * Returned intervals are proposals; they do not grant a checked status. */
export function compileIntervalFrame(arithmetic: IntervalArithmetic, input: unknown, query: EvidenceQuery) {
    // Bound lists before strict parsing performs reference searches.
    if (!input || typeof input !== 'object') throw Error('Malformed frame source.');
    const outer = input as Record<string, unknown>;
    const raw = (outer.version === 2 ? outer.model : outer) as Record<string, unknown>;
    if (!raw || typeof raw !== 'object') throw Error('Malformed frame source.');
    for (const name of ['nodes', 'members', 'supports', 'loads'] as const)
        if (Array.isArray(raw[name]) && raw[name].length > frameLimits[name]) throw Error('Limit: source list exceeds frame budget.');
    const model = parseEvidenceModel(input);
    for (const items of [model.nodes, model.members, model.supports, model.loads]) {
        for (const item of items) {
            if (item.id.length > 256) throw Error('Limit: at most 256 UTF-16 code units in an identifier.');
        }
    }
    if (!model.members.length) throw Error('Unsupported: draw at least one member.');
    for (const node of model.nodes) {
        if (node.joint !== 'rigid') throw Error('Unsupported: enclosure path requires rigid joints.');
        if (!model.members.some(member => member.a === node.id || member.b === node.id)) throw Error('Unsupported: isolated node.');
    }
    for (const member of model.members)
        for (const connection of [member.connectionA, member.connectionB])
            if (connection && Object.values(connection).some(value => value !== 'rigid')) throw Error('Unsupported: released or elastic connection.');
    if (!model.members.some(member => member.id === query.member) || !Number.isFinite(query.parameter) || query.parameter < 0 || query.parameter > 1)
        throw Error('Malformed query: invalid member or parameter.');
    if (!['left', 'right'].includes(query.cutSide) || (query.parameter === 0 && query.cutSide !== 'right') || (query.parameter === 1 && query.cutSide !== 'left'))
        throw Error('Unsupported: select the interior endpoint limit or an explicit interior side.');
    for (const name of ['quantity', 'units', 'signConvention'] as const)
        if (query[name] !== frameQueryConvention[name]) throw Error('Unsupported: query convention mismatch.');

    const constant = (n: number) => arithmetic.bounds(integer(n));
    const zeros = (rows: number, columns = rows): IntervalMatrix => Array.from({ length: rows }, () => Array.from({ length: columns }, () => constant(0)));
    const plus = arithmetic.add.bind(arithmetic);
    const minus = arithmetic.negate.bind(arithmetic);
    const times = arithmetic.multiply.bind(arithmetic);
    const over = arithmetic.divide.bind(arithmetic);
    const points: FramePoint[] = model.nodes.map((node, index) => ({ owner: 'node', index, t: zero, x: binary64(node.x), y: binary64(node.y) }));
    const segments: EnclosedSegment[] = [];
    const locations: Map<string, number>[] = [];
    // 1. Split each original member at its support and load boundaries.
    // Interior points belong to that member; coincident geometry alone does not join them.
    for (const [memberIndex, member] of model.members.entries()) {
        const a = model.nodes.findIndex(node => node.id === member.a);
        const b = model.nodes.findIndex(node => node.id === member.b);
        const dx = sub(points[b].x, points[a].x);
        const dy = sub(points[b].y, points[a].y);
        const geometry = memberGeometry(arithmetic, dx, dy);
        const cuts = new Map<string, Fraction>([[key(zero), zero], [key(one), one]]);
        const insert = (value: number) => {
            const t = binary64(value);
            cuts.set(key(t), t);
        };
        model.supports.filter(support => support.member === member.id).forEach(support => insert(support.t));
        for (const load of model.loads) if (load.member === member.id) {
            insert(load.t);
            if (load.kind === 'distributed') insert(load.end);
        }
        const ordered = [...cuts.values()].sort(compare);
        const pointAt = new Map<string, number>();
        for (const t of ordered) {
            const index = equal(t, zero) ? a : equal(t, one) ? b : points.length;
            if (!equal(t, zero) && !equal(t, one)) {
                if (points.length >= frameLimits.points) throw Error('Limit: active point count.');
                points.push({ owner: 'member', index: memberIndex, t, x: add(points[a].x, mul(t, dx)), y: add(points[a].y, mul(t, dy)) });
            }
            pointAt.set(key(t), index);
        }
        locations.push(pointAt);
        for (let i = 0; i + 1 < ordered.length; i++) {
            if (segments.length >= frameLimits.segments) throw Error('Limit: segment count.');
            const from = ordered[i];
            const to = ordered[i + 1];
            let vertical = zero;
            let verticalEnd = zero;
            for (const load of model.loads) {
                if (load.member !== member.id || load.kind !== 'distributed') continue;
                const loadFrom = binary64(load.t);
                const loadTo = binary64(load.end);
                if (compare(loadFrom, from) > 0 || compare(to, loadTo) > 0) continue;
                const startIntensity = binary64(load.fy);
                const change = sub(binary64(load.qEnd), startIntensity);
                const intensity = (t: Fraction) => {
                    const position = div(sub(t, loadFrom), sub(loadTo, loadFrom));
                    return add(startIntensity, mul(change, position));
                };
                vertical = add(vertical, intensity(from));
                verticalEnd = add(verticalEnd, intensity(to));
            }
            // 2. Form local stiffness and consistent loads before rotation.
            // Intensities are global vertical force per physical member length.
            const length = times(geometry.length, arithmetic.bounds(sub(to, from)));
            const EA = binary64(member.EA);
            const EI = binary64(member.EI);
            const axial = over(arithmetic.bounds(EA), length);
            const lengthSquared = times(length, length);
            const bend = over(times(constant(12), arithmetic.bounds(EI)), times(lengthSquared, length));
            const coupling = over(times(constant(6), arithmetic.bounds(EI)), lengthSquared);
            const rotation = over(times(constant(4), arithmetic.bounds(EI)), length);
            const half = over(rotation, constant(2));
            const z = constant(0);
            const localStiffness = [
                [axial, z, z, minus(axial), z, z],
                [z, bend, coupling, z, minus(bend), coupling],
                [z, coupling, rotation, z, minus(coupling), half],
                [minus(axial), z, z, axial, z, z],
                [z, minus(bend), minus(coupling), z, bend, minus(coupling)],
                [z, coupling, half, z, minus(coupling), rotation],
            ];
            const p0 = times(geometry.sine, arithmetic.bounds(vertical));
            const p1 = times(geometry.sine, arithmetic.bounds(verticalEnd));
            const q0 = times(geometry.cosine, arithmetic.bounds(vertical));
            const q1 = times(geometry.cosine, arithmetic.bounds(verticalEnd));
            const weighted = (x: RationalInterval, y: RationalInterval, u: number, v: number) => plus(times(constant(u), x), times(constant(v), y));
            const localForce = [
                over(times(length, weighted(p0, p1, 2, 1)), constant(6)),
                over(times(length, weighted(q0, q1, 7, 3)), constant(20)),
                over(times(lengthSquared, weighted(q0, q1, 3, 2)), constant(60)),
                over(times(length, weighted(p0, p1, 1, 2)), constant(6)),
                over(times(length, weighted(q0, q1, 3, 7)), constant(20)),
                minus(over(times(lengthSquared, weighted(q0, q1, 2, 3)), constant(60))),
            ];
            const transform = zeros(6);
            for (const offset of [0,3]) {
                transform[offset][offset] = geometry.cosine;
                transform[offset][offset + 1] = geometry.sine;
                transform[offset + 1][offset] = minus(geometry.sine);
                transform[offset + 1][offset + 1] = geometry.cosine;
                transform[offset + 2][offset + 2] = constant(1);
            }
            segments.push({ member: memberIndex, start: pointAt.get(key(from))!, end: pointAt.get(key(to))!, from, to,
                length, cosine: geometry.cosine, sine: geometry.sine, vertical, verticalEnd, EA, EI, localStiffness, localForce, transform });
        }
    }
    // 3. Assemble global K = Σ TᵀkT and F = Σ Tᵀf, then add point actions.
    const count = 3 * points.length;
    const stiffness = zeros(count);
    const force = Array.from({ length: count }, () => constant(0));
    for (const segment of segments) {
        const indices = [3*segment.start,3*segment.start+1,3*segment.start+2,3*segment.end,3*segment.end+1,3*segment.end+2];
        const transformed = segment.localStiffness.map(row => segment.transform[0].map((_, j) => intervalDot(arithmetic, row, segment.transform.map(entry => entry[j]))));
        for (let i = 0; i < 6; i++) {
            const column = segment.transform.map(row => row[i]);
            force[indices[i]] = plus(force[indices[i]], intervalDot(arithmetic, column, segment.localForce));
            for (let j = 0; j < 6; j++) {
                const contribution = intervalDot(arithmetic, column, transformed.map(row => row[j]));
                stiffness[indices[i]][indices[j]] = plus(stiffness[indices[i]][indices[j]], contribution);
            }
        }
    }
    const locate = (member: string, t: number) => locations[model.members.findIndex(item => item.id === member)].get(key(binary64(t)))!;
    for (const load of model.loads) if (load.kind !== 'distributed') {
        const index = locate(load.member, load.t);
        const values = load.kind === 'force' ? [load.fx,load.fy,0] : [0,0,load.mz];
        values.forEach((value, direction) => { force[3*index+direction] = plus(force[3*index+direction], arithmetic.bounds(binary64(value))); });
    }
    // 4. Retain every support at its owned point and assemble admissible coordinates.
    const supportPoints = model.supports.map(support => locate(support.member, support.t));
    const bases = points.map((_, index) => pointBasis(arithmetic, model.supports.filter((_, i) => supportPoints[i] === index)));
    const coordinates = bases.flatMap((basis, point) => basis.columns.map(column => ({ point, ...column })));
    const basis = zeros(count, coordinates.length);
    coordinates.forEach((column, j) => column.components.forEach((component, i) => { basis[3*column.point+i][j] = component; }));
    const stiffnessBasis = stiffness.map(row => coordinates.map((_, j) => intervalDot(arithmetic, row, basis.map(entry => entry[j]))));
    const reduced = coordinates.map((_, i) => coordinates.map((_, j) => intervalDot(arithmetic, basis.map(row => row[i]), stiffnessBasis.map(row => row[j]))));
    const reducedForce = coordinates.map((_, i) => intervalDot(arithmetic, basis.map(row => row[i]), force));
    return { model, query: { ...query }, points, segments, supportPoints, bases, coordinates, basis, stiffness, force, reduced, reducedForce };
}
