/** Linear 2D Euler–Bernoulli frame analysis. Units: m, kN, kN m, radians.
 * Global y and rotations are positive upwards and counterclockwise.
 * Member x runs from a to b; member y is its counterclockwise normal.
 * Section conventions: tension N > 0, sagging M > 0, and dM/dx = V.
 */
export interface Point {
    id: string;
    x: number;
    y: number;
}
export interface Member {
    id: string;
    a: string;
    b: string;
    EA: number;
    EI: number;
}
export interface Support {
    id: string;
    member: string;
    t: number;
    kind: 'pin' | 'roller' | 'fixed';
    angle: number;
}
export interface Load {
    id: string;
    member: string;
    kind: 'force' | 'moment' | 'distributed';
    t: number;
    end: number;
    fx: number;
    fy: number;
    mz: number;
    qEnd: number;
}
export interface Model {
    nodes: Point[];
    members: Member[];
    supports: Support[];
    loads: Load[];
}
export interface Sample {
    x: number;
    y: number;
    t: number;
    N: number;
    V: number;
    M: number;
    ux: number;
    uy: number;
    rotation: number;
}
export interface ElementResult {
    member: string;
    t0: number;
    t1: number;
    length: number;
    c: number;
    s: number;
    samples: Sample[];
}
export interface Reaction {
    x: number;
    y: number;
    fx: number;
    fy: number;
    mz: number;
    supports: string[];
}
export interface Analysis {
    status: 'stable' | 'unstable' | 'empty' | 'invalid';
    message: string;
    degree?: number;
    elements: ElementResult[];
    reactions: Reaction[];
    mechanism?: {
        x: number;
        y: number;
        ux: number;
        uy: number;
        rotation: number;
    }[];
    residual?: number;
}
const tolerance = 1e-8;
const zeros = (rows: number, columns: number): number[][] => Array.from({ length: rows }, () => Array(columns).fill(0));
const dot = (a: number[], b: number[]) => a.reduce((sum, value, i) => sum + value * b[i], 0);
const multiplyVector = (a: number[][], b: number[]) => a.map(row => dot(row, b));
const clamp = (value: number) => Math.max(0, Math.min(1, value));
export function position(model: Model, memberId: string, t: number): {
    x: number;
    y: number;
} {
    const member = model.members.find(item => item.id === memberId)!;
    const a = model.nodes.find(node => node.id === member.a)!;
    const b = model.nodes.find(node => node.id === member.b)!;
    return { x: a.x + t * (b.x - a.x), y: a.y + t * (b.y - a.y) };
}
/** Row reduction supplies a null vector as well as a solution. A mechanism is
 * reported even if the current load happens to be orthogonal to that motion. */
function reduce(matrix: number[][], rhs: number[]) {
    const size = rhs.length;
    const work = matrix.map((row, index) => [...row, rhs[index]]);
    const pivots: number[] = [];
    let row = 0;
    for (let column = 0; column < size && row < size; column++) {
        let best = row;
        for (let next = row + 1; next < size; next++) {
            if (Math.abs(work[next][column]) > Math.abs(work[best][column]))
                best = next;
        }
        if (Math.abs(work[best][column]) < 1e-10)
            continue;
        [work[row], work[best]] = [work[best], work[row]];
        const divisor = work[row][column];
        for (let j = column; j <= size; j++)
            work[row][j] /= divisor;
        for (let other = 0; other < size; other++) {
            if (other === row)
                continue;
            const factor = work[other][column];
            for (let j = column; j <= size; j++)
                work[other][j] -= factor * work[row][j];
        }
        pivots.push(column);
        row++;
    }
    const solution = Array(size).fill(0);
    pivots.forEach((column, index) => { solution[column] = work[index][size]; });
    const freeColumn = Array.from({ length: size }, (_, i) => i).find(i => !pivots.includes(i));
    const nullVector = Array(size).fill(0);
    if (freeColumn !== undefined) {
        nullVector[freeColumn] = 1;
        pivots.forEach((column, index) => { nullVector[column] = -work[index][freeColumn]; });
    }
    return { solution, nullVector, rank: row };
}
function elementStiffness(EA: number, EI: number, length: number): number[][] {
    const axial = EA / length;
    const bending = 12 * EI / length ** 3;
    const coupling = 6 * EI / length ** 2;
    const rotation = 4 * EI / length;
    return [
        [axial, 0, 0, -axial, 0, 0],
        [0, bending, coupling, 0, -bending, coupling],
        [0, coupling, rotation, 0, -coupling, rotation / 2],
        [-axial, 0, 0, axial, 0, 0],
        [0, -bending, -coupling, 0, bending, -coupling],
        [0, coupling, rotation / 2, 0, -coupling, rotation],
    ];
}
interface Segment {
    member: Member;
    t0: number;
    t1: number;
    i: number;
    j: number;
    length: number;
    c: number;
    s: number;
    stiffness: number[][];
    transform: number[][];
    equivalent: number[];
    qx0: number;
    qx1: number;
    qy0: number;
    qy1: number;
}
export function analyse(model: Model): Analysis {
    const fail = (status: Analysis['status'], message: string): Analysis => ({ status, message, elements: [], reactions: [] });
    if (!model.members.length)
        return fail('empty', 'Draw a member, then place supports and loads.');
    if (model.members.length > 60 || model.loads.length > 100 || model.supports.length > 60)
        return fail('invalid', 'This release supports up to 60 members, 60 supports, and 100 loads.');
    if (new Set(model.nodes.map(n => n.id)).size !== model.nodes.length || new Set(model.members.map(m => m.id)).size !== model.members.length)
        return fail('invalid', 'Node and member identifiers must be unique.');
    if (model.nodes.some(node => !Number.isFinite(node.x + node.y)))
        return fail('invalid', 'Coordinates must be finite.');
    for (const member of model.members) {
        const a = model.nodes.find(n => n.id === member.a);
        const b = model.nodes.find(n => n.id === member.b);
        if (!a || !b || Math.hypot(a.x - b.x, a.y - b.y) < 0.02)
            return fail('invalid', 'Each member must connect two distinct joints at least 0.02 m apart.');
        if (!(member.EA > 0 && member.EI > 0 && Number.isFinite(member.EA + member.EI)))
            return fail('invalid', 'EA and EI must be positive finite values.');
    }
    for (const item of [...model.supports, ...model.loads]) {
        if (!model.members.some(m => m.id === item.member) || !Number.isFinite(item.t) || item.t < 0 || item.t > 1)
            return fail('invalid', 'Every support and load must lie on a member.');
    }
    if (model.supports.some(s => !['pin', 'roller', 'fixed'].includes(s.kind) || !Number.isFinite(s.angle)))
        return fail('invalid', 'Invalid support definition.');
    for (const load of model.loads) {
        if (![load.fx, load.fy, load.mz, load.end, load.qEnd].every(Number.isFinite))
            return fail('invalid', 'Load components must be finite.');
        if (load.kind === 'distributed' && !(load.end > load.t && load.end <= 1))
            return fail('invalid', 'Distributed loads require a positive interval on the member.');
    }
    // 1. Subdivide at load/support positions. Interior nodes belong to their
    // member; crossing members do not connect unless they share a drawn joint.
    const points: {
        x: number;
        y: number;
    }[] = [];
    const indices = new Map<string, number>();
    const key = (member: Member, t: number) => t < tolerance ? member.a : t > 1 - tolerance ? member.b : `${member.id}@${t.toFixed(8)}`;
    function nodeIndex(member: Member, t: number): number {
        const nodeKey = key(member, t);
        if (!indices.has(nodeKey)) {
            indices.set(nodeKey, points.length);
            points.push(position(model, member.id, t));
        }
        return indices.get(nodeKey)!;
    }
    const segments: Segment[] = [];
    for (const member of model.members) {
        const locations = [0, 1, ...model.supports.filter(s => s.member === member.id).map(s => s.t)];
        model.loads.filter(l => l.member === member.id).forEach(load => {
            locations.push(load.t);
            if (load.kind === 'distributed')
                locations.push(load.end);
        });
        const cuts = [...new Set(locations.map(t => Number(clamp(t).toFixed(8))))].sort((a, b) => a - b);
        for (let part = 0; part < cuts.length - 1; part++) {
            const t0 = cuts[part], t1 = cuts[part + 1];
            const i = nodeIndex(member, t0), j = nodeIndex(member, t1);
            const dx = points[j].x - points[i].x, dy = points[j].y - points[i].y;
            const length = Math.hypot(dx, dy), c = dx / length, s = dy / length;
            const transform = [[c, s, 0, 0, 0, 0], [-s, c, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, c, s, 0], [0, 0, 0, -s, c, 0], [0, 0, 0, 0, 0, 1]];
            let qyGlobal0 = 0, qyGlobal1 = 0;
            for (const load of model.loads.filter(l => l.member === member.id && l.kind === 'distributed')) {
                const middle = (t0 + t1) / 2;
                if (middle > load.t && middle < load.end) {
                    qyGlobal0 += load.fy + (load.qEnd - load.fy) * (t0 - load.t) / (load.end - load.t);
                    qyGlobal1 += load.fy + (load.qEnd - load.fy) * (t1 - load.t) / (load.end - load.t);
                }
            }
            const qx0 = s * qyGlobal0, qx1 = s * qyGlobal1;
            const qy0 = c * qyGlobal0, qy1 = c * qyGlobal1;
            const equivalent = [length * (2 * qx0 + qx1) / 6, length * (7 * qy0 + 3 * qy1) / 20, length ** 2 * (3 * qy0 + 2 * qy1) / 60,
                length * (qx0 + 2 * qx1) / 6, length * (3 * qy0 + 7 * qy1) / 20, -(length ** 2) * (2 * qy0 + 3 * qy1) / 60];
            segments.push({ member, t0, t1, i, j, length, c, s, transform, equivalent, qx0, qx1, qy0, qy1, stiffness: elementStiffness(member.EA, member.EI, length) });
        }
    }
    const dofs = 3 * points.length;
    const stiffness = zeros(dofs, dofs), force = Array(dofs).fill(0);
    for (const segment of segments) {
        const map = [3 * segment.i, 3 * segment.i + 1, 3 * segment.i + 2, 3 * segment.j, 3 * segment.j + 1, 3 * segment.j + 2];
        const { transform: T, stiffness: k } = segment;
        for (let a = 0; a < 6; a++) {
            for (let local = 0; local < 6; local++)
                force[map[a]] += T[local][a] * segment.equivalent[local];
            for (let b = 0; b < 6; b++) {
                let entry = 0;
                for (let u = 0; u < 6; u++)
                    for (let v = 0; v < 6; v++)
                        entry += T[u][a] * k[u][v] * T[v][b];
                stiffness[map[a]][map[b]] += entry;
            }
        }
    }
    for (const load of model.loads.filter(l => l.kind !== 'distributed')) {
        const member = model.members.find(m => m.id === load.member)!;
        const index = nodeIndex(member, Number(load.t.toFixed(8)));
        if (load.kind === 'force') {
            force[3 * index] += load.fx;
            force[3 * index + 1] += load.fy;
        }
        else
            force[3 * index + 2] += load.mz;
    }
    // 2. Construct an orthonormal basis of allowable nodal movements. Inclined
    // rollers impose a displacement constraint along their reaction direction.
    const basis: number[][] = [], supportGroups = new Map<number, Support[]>();
    let restrained = 0;
    model.supports.forEach(support => {
        const member = model.members.find(m => m.id === support.member)!;
        const index = nodeIndex(member, Number(support.t.toFixed(8)));
        supportGroups.set(index, [...(supportGroups.get(index) || []), support]);
    });
    points.forEach((_, index) => {
        const constraints: number[][] = [];
        for (const support of supportGroups.get(index) || []) {
            if (support.kind === 'fixed' || support.kind === 'pin')
                constraints.push([1, 0, 0], [0, 1, 0]);
            if (support.kind === 'fixed')
                constraints.push([0, 0, 1]);
            if (support.kind === 'roller')
                constraints.push([Math.cos(support.angle * Math.PI / 180), Math.sin(support.angle * Math.PI / 180), 0]);
        }
        const blocked: number[][] = [];
        for (const constraint of constraints) {
            let residual = [...constraint];
            blocked.forEach(vector => { const projection = dot(residual, vector); residual = residual.map((v, i) => v - projection * vector[i]); });
            const norm = Math.hypot(...residual);
            if (norm > tolerance)
                blocked.push(residual.map(v => v / norm));
        }
        restrained += blocked.length;
        const allowed: number[][] = [];
        for (const candidate of [[1, 0, 0], [0, 1, 0], [0, 0, 1]]) {
            let residual = [...candidate];
            [...blocked, ...allowed].forEach(vector => { const projection = dot(residual, vector); residual = residual.map((v, i) => v - projection * vector[i]); });
            const norm = Math.hypot(...residual);
            if (norm > tolerance) {
                const vector = residual.map(v => v / norm);
                allowed.push(vector);
                const full = Array(dofs).fill(0);
                vector.forEach((value, component) => { full[3 * index + component] = value; });
                basis.push(full);
            }
        }
    });
    const products = basis.map(vector => multiplyVector(stiffness, vector));
    const reduced = basis.map(a => products.map(b => dot(a, b)));
    const scales = basis.map((_, i) => Math.sqrt(Math.abs(reduced[i][i])) || 1);
    const scaled = reduced.map((row, i) => row.map((value, j) => value / (scales[i] * scales[j])));
    const answer = reduce(scaled, basis.map((vector, i) => dot(vector, force) / scales[i]));
    const expand = (coordinates: number[]) => Array.from({ length: dofs }, (_, j) => basis.reduce((sum, vector, i) => sum + vector[j] * coordinates[i] / scales[i], 0));
    if (answer.rank < basis.length) {
        const motion = expand(answer.nullVector);
        const extent = Math.max(...segments.map(segment => segment.length), 1);
        const normalizer = Math.max(...points.map((_, i) => Math.hypot(motion[3 * i], motion[3 * i + 1], extent * motion[3 * i + 2])), 1e-20);
        return { ...fail('unstable', 'Unstable: a free motion remains. Add or reorient a restraint; the highlighted motion is a linear mechanism, not a buckling prediction.'),
            mechanism: points.map((p, i) => ({ ...p, ux: motion[3 * i] / normalizer, uy: motion[3 * i + 1] / normalizer, rotation: motion[3 * i + 2] / normalizer })) };
    }
    const displacement = expand(answer.solution);
    const imbalance = multiplyVector(stiffness, displacement).map((value, i) => value - force[i]);
    const residual = Math.max(0, ...basis.map(vector => Math.abs(dot(vector, imbalance)))) / Math.max(1, ...force.map(Math.abs));
    if (!Number.isFinite(residual) || residual > 1e-6)
        return fail('invalid', 'The model is poorly conditioned. Check very short members and stiffness differences.');
    // 3. Recover section forces from equilibrium, then integrate them. The load
    // particular solution is retained, giving exact polynomial deflections for
    // each prismatic segment with linear distributed loading.
    const elements = segments.map(segment => {
        const { i, j, length: L, c, s, member } = segment;
        const global = [displacement[3 * i], displacement[3 * i + 1], displacement[3 * i + 2], displacement[3 * j], displacement[3 * j + 1], displacement[3 * j + 2]];
        const local = multiplyVector(segment.transform, global);
        const actions = multiplyVector(segment.stiffness, local).map((v, k) => v - segment.equivalent[k]);
        const qxSlope = (segment.qx1 - segment.qx0) / L, qySlope = (segment.qy1 - segment.qy0) / L;
        const samples: Sample[] = Array.from({ length: 41 }, (_, step) => {
            const x = L * step / 40;
            const N = -actions[0] - segment.qx0 * x - qxSlope * x * x / 2;
            const V = actions[1] + segment.qy0 * x + qySlope * x * x / 2;
            const M = -actions[2] + actions[1] * x + segment.qy0 * x * x / 2 + qySlope * x ** 3 / 6;
            const u = local[0] + (-actions[0] * x - segment.qx0 * x * x / 2 - qxSlope * x ** 3 / 6) / member.EA;
            const v = local[1] + local[2] * x + (-actions[2] * x * x / 2 + actions[1] * x ** 3 / 6 + segment.qy0 * x ** 4 / 24 + qySlope * x ** 5 / 120) / member.EI;
            const rotation = local[2] + (-actions[2] * x + actions[1] * x * x / 2 + segment.qy0 * x ** 3 / 6 + qySlope * x ** 4 / 24) / member.EI;
            return { x: points[i].x + c * x, y: points[i].y + s * x, t: segment.t0 + (segment.t1 - segment.t0) * step / 40, N, V, M, ux: c * u - s * v, uy: s * u + c * v, rotation };
        });
        return { member: member.id, t0: segment.t0, t1: segment.t1, length: L, c, s, samples };
    });
    const degree = 3 * segments.length + restrained - 3 * points.length;
    return { status: 'stable', message: degree === 0 ? 'Stable · statically determinate' : `Stable · statically indeterminate (degree ${degree})`, degree, elements, residual,
        reactions: [...supportGroups].map(([index, supports]) => ({ ...points[index], fx: imbalance[3 * index], fy: imbalance[3 * index + 1], mz: imbalance[3 * index + 2], supports: supports.map(s => s.id) })) };
}
/** Splitting a drawn member creates a rigid joint and remaps attached objects. */
export function splitMember(model: Model, memberId: string, t: number, nodeId: string): string {
    const member = model.members.find(m => m.id === memberId)!;
    if (t < 1e-6)
        return member.a;
    if (t > 1 - 1e-6)
        return member.b;
    const point = position(model, memberId, t);
    model.nodes.push({ id: nodeId, ...point });
    const secondId = `${memberId}-${nodeId}`;
    const second: Member = { ...member, id: secondId, a: nodeId };
    member.b = nodeId;
    model.members.push(second);
    for (const support of model.supports.filter(s => s.member === memberId)) {
        if (support.t <= t)
            support.t /= t;
        else {
            support.member = secondId;
            support.t = (support.t - t) / (1 - t);
        }
    }
    const extra: Load[] = [];
    for (const load of model.loads.filter(l => l.member === memberId)) {
        if (load.kind === 'distributed') {
            if (load.end <= t) {
                load.t /= t;
                load.end /= t;
            }
            else if (load.t >= t) {
                load.member = secondId;
                load.t = (load.t - t) / (1 - t);
                load.end = (load.end - t) / (1 - t);
            }
            else {
                const atCut = load.fy + (load.qEnd - load.fy) * (t - load.t) / (load.end - load.t);
                extra.push({ ...load, id: `${load.id}-${nodeId}`, member: secondId, t: 0, end: (load.end - t) / (1 - t), fy: atCut });
                load.t /= t;
                load.end = 1;
                load.qEnd = atCut;
            }
        }
        else if (load.t <= t)
            load.t /= t;
        else {
            load.member = secondId;
            load.t = (load.t - t) / (1 - t);
        }
    }
    model.loads.push(...extra);
    return nodeId;
}
export function example(name = 'beam'): Model {
    const model: Model = { nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 8, y: 0 }], members: [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }], supports: [], loads: [] };
    model.supports = [{ id: 'S1', member: 'AB', t: 0, kind: name === 'cantilever' ? 'fixed' : 'pin', angle: 90 }];
    if (name !== 'cantilever')
        model.supports.push({ id: 'S2', member: 'AB', t: 1, kind: 'roller', angle: 90 });
    model.loads = [{ id: 'P1', member: 'AB', kind: 'force', t: name === 'cantilever' ? 1 : 0.5, end: 1, fx: 0, fy: -20, mz: 0, qEnd: -5 }];
    if (name === 'udl')
        model.loads = [{ id: 'q1', member: 'AB', kind: 'distributed', t: 0, end: 1, fx: 0, fy: -5, mz: 0, qEnd: -5 }];
    if (name === 'overhang') {
        model.supports[0].t = 0.2;
        model.supports[1].t = 0.8;
        model.loads[0].t = 1;
    }
    if (name === 'frame') {
        model.nodes = [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 0, y: 4 }, { id: 'C', x: 6, y: 4 }, { id: 'D', x: 6, y: 0 }];
        model.members = [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }, { id: 'BC', a: 'B', b: 'C', EA: 2000000, EI: 20000 }, { id: 'CD', a: 'C', b: 'D', EA: 2000000, EI: 20000 }];
        model.supports = [{ id: 'S1', member: 'AB', t: 0, kind: 'fixed', angle: 90 }, { id: 'S2', member: 'CD', t: 1, kind: 'fixed', angle: 90 }];
        model.loads = [{ id: 'q1', member: 'BC', kind: 'distributed', t: 0, end: 1, fx: 0, fy: -5, mz: 0, qEnd: -5 }];
    }
    return model;
}
