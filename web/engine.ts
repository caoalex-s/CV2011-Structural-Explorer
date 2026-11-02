/** Linear 2D Euler–Bernoulli frame analysis. Units: m, kN, kN m, radians.
 * Global y and rotations are positive upwards and counterclockwise.
 * Member x runs from a to b; member y is its counterclockwise normal.
 * Section conventions: tension N > 0, sagging M > 0, and dM/dx = V.
 */
export interface Point {
    id: string;
    x: number;
    y: number;
    joint?: 'rigid' | 'pinned' | 'semi-rigid' | 'custom';
    rotationStiffness?: number;
    referenceMember?: string;
}
/** End connections relate a member end to the reference member at its joint.
 * Translations are resolved along this member's local axial/transverse axes.
 * A number is a positive spring stiffness (kN/m or kN m/rad). */
export type ConnectionRule = 'rigid' | 'free' | number;
export interface Connection {
    axial: ConnectionRule;
    transverse: ConnectionRule;
    rotation: ConnectionRule;
}
export interface Member {
    id: string;
    a: string;
    b: string;
    EA: number;
    EI: number;
    connectionA?: Connection;
    connectionB?: Connection;
}
export interface Support {
    id: string;
    member: string;
    t: number;
    kind: 'pin' | 'roller' | 'fixed' | 'guided' | 'custom';
    angle: number;
    fixX?: boolean;
    fixY?: boolean;
    fixRotation?: boolean;
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
    connections?: { node: string; member: string; end: 'a' | 'b'; axialSlip: number; transverseSlip: number; relativeRotation: number; axialForce: number; transverseForce: number; moment: number }[];
}
export const rigidConnection = (): Connection => ({ axial: 'rigid', transverse: 'rigid', rotation: 'rigid' });
export function referenceMember(model: Model, nodeId: string): string | undefined {
    const connected = model.members.filter(member => member.a === nodeId || member.b === nodeId);
    const requested = model.nodes.find(node => node.id === nodeId)?.referenceMember;
    return connected.find(member => member.id === requested)?.id || connected[0]?.id;
}
export function endConnection(model: Model, member: Member, end: 'a' | 'b'): Connection {
    if (referenceMember(model, member[end]) === member.id) return rigidConnection();
    const explicit = end === 'a' ? member.connectionA : member.connectionB;
    if (explicit) return explicit;
    const node = model.nodes.find(node => node.id === member[end])!;
    return { axial: 'rigid', transverse: 'rigid', rotation: node.joint === 'pinned' ? 'free' : node.joint === 'semi-rigid' ? node.rotationStiffness ?? 20000 : 'rigid' };
}
/** Presentation labels are separate from stable model IDs and never enter equations. */
export function nodeLabel(index: number): string {
    let label = '';
    for (let value = index + 1; value > 0; value = Math.floor((value - 1) / 26))
        label = String.fromCharCode(65 + (value - 1) % 26) + label;
    return label;
}
export function nodeLabels(model: Model): Map<string, string> {
    return new Map(model.nodes.map((node, index) => [node.id, nodeLabel(index)]));
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
    mapping?: number[][];
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
    for (const node of model.nodes) {
        if (node.joint && !['rigid', 'pinned', 'semi-rigid', 'custom'].includes(node.joint))
            return fail('invalid', 'Unknown joint type.');
        if (node.joint === 'semi-rigid' && !(Number.isFinite(node.rotationStiffness ?? 20000) && (node.rotationStiffness ?? 20000) > 0))
            return fail('invalid', 'A semi-rigid joint needs a positive finite rotational stiffness.');
    }
    for (const member of model.members) {
        const a = model.nodes.find(n => n.id === member.a);
        const b = model.nodes.find(n => n.id === member.b);
        if (!a || !b || Math.hypot(a.x - b.x, a.y - b.y) < 0.02)
            return fail('invalid', 'Each member must connect two distinct joints at least 0.02 m apart.');
        if (!(member.EA > 0 && member.EI > 0 && Number.isFinite(member.EA + member.EI)))
            return fail('invalid', 'EA and EI must be positive finite values.');
        for (const connection of [member.connectionA, member.connectionB]) {
            if (connection && ![connection.axial, connection.transverse, connection.rotation].every(rule => rule === 'rigid' || rule === 'free' || (typeof rule === 'number' && Number.isFinite(rule) && rule > 0)))
                return fail('invalid', 'Connection directions must be rigid, released, or a positive finite spring stiffness.');
        }
    }
    for (const item of [...model.supports, ...model.loads]) {
        if (!model.members.some(m => m.id === item.member) || !Number.isFinite(item.t) || item.t < 0 || item.t > 1)
            return fail('invalid', 'Every support and load must lie on a member.');
    }
    if (model.supports.some(s => !['pin', 'roller', 'fixed', 'guided', 'custom'].includes(s.kind) || !Number.isFinite(s.angle)))
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
    // 2. Add relative end movements to a physical reference member at each
    // joint. This avoids an unused central rotation at a fully pinned joint.
    // Rigid directions are tied exactly; released directions have no stiffness.
    // A finite spring contributes k * (relative movement)^2 / 2 to the energy.
    let dofs = 3 * points.length;
    const directions = ['axial', 'transverse', 'rotation'] as const;
    const flexibleEnds: { member: Member; end: 'a' | 'b'; rule: Connection; indices: number[] }[] = [];
    for (const member of model.members) {
        for (const end of ['a', 'b'] as const) {
            const rule = endConnection(model, member, end);
            if (directions.some(direction => rule[direction] !== 'rigid'))
                flexibleEnds.push({ member, end, rule, indices: directions.map(direction => rule[direction] === 'rigid' ? -1 : dofs++) });
        }
    }
    function endMapping(member: Member, t: number): number[][] {
        const index = nodeIndex(member, Number(t.toFixed(8)));
        const mapping = zeros(3, dofs);
        for (let direction = 0; direction < 3; direction++) mapping[direction][3 * index + direction] = 1;
        const end = t < tolerance ? 'a' : t > 1 - tolerance ? 'b' : null;
        const flexible = flexibleEnds.find(item => item.member.id === member.id && item.end === end);
        if (flexible) {
            const a = position(model, member.id, 0), b = position(model, member.id, 1);
            const length = Math.hypot(b.x - a.x, b.y - a.y), c = (b.x - a.x) / length, s = (b.y - a.y) / length;
            const [axial, transverse, rotation] = flexible.indices;
            if (axial >= 0) { mapping[0][axial] = c; mapping[1][axial] = s; }
            if (transverse >= 0) { mapping[0][transverse] = -s; mapping[1][transverse] = c; }
            if (rotation >= 0) mapping[2][rotation] = 1;
        }
        return mapping;
    }
    const stiffness = zeros(dofs, dofs), force = Array(dofs).fill(0);
    let springCount = 0;
    for (const flexible of flexibleEnds) directions.forEach((direction, i) => {
        const rule = flexible.rule[direction];
        if (typeof rule === 'number') { stiffness[flexible.indices[i]][flexible.indices[i]] += rule; springCount++; }
    });
    for (const segment of segments) {
        const globalMapping = [...endMapping(segment.member, segment.t0), ...endMapping(segment.member, segment.t1)];
        segment.mapping = segment.transform.map(row => Array.from({ length: dofs }, (_, column) => row.reduce((sum, value, i) => sum + value * globalMapping[i][column], 0)));
        const entries = segment.mapping.map(row => row.flatMap((value, index) => Math.abs(value) > 1e-15 ? [{ index, value }] : []));
        for (let a = 0; a < 6; a++) for (const left of entries[a]) {
            force[left.index] += left.value * segment.equivalent[a];
            for (let b = 0; b < 6; b++) for (const right of entries[b])
                stiffness[left.index][right.index] += left.value * segment.stiffness[a][b] * right.value;
        }
    }
    // An action belongs to the selected member side of a joint. In particular,
    // a couple at a hinge acts on that member end, not on a fictitious hub.
    for (const load of model.loads.filter(l => l.kind !== 'distributed')) {
        const member = model.members.find(m => m.id === load.member)!;
        const mapping = endMapping(member, load.t);
        const components = load.kind === 'force' ? [load.fx, load.fy, 0] : [0, 0, load.mz];
        for (let column = 0; column < dofs; column++)
            force[column] += components.reduce((sum, value, direction) => sum + value * mapping[direction][column], 0);
    }
    // 3. Ground constraints act on the selected member side as well. Build
    // their nullspace so inclined guides and released ends are treated exactly.
    const constraints: { row: number[]; direction: number[]; support: Support; index: number }[] = [];
    const supportGroups = new Map<number, Support[]>();
    for (const support of model.supports) {
        const member = model.members.find(m => m.id === support.member)!;
        const index = nodeIndex(member, Number(support.t.toFixed(8)));
        supportGroups.set(index, [...(supportGroups.get(index) || []), support]);
        const mapping = endMapping(member, support.t), blockedDirections: number[][] = [];
        if (['fixed', 'pin'].includes(support.kind) || support.kind === 'custom' && support.fixX) blockedDirections.push([1, 0, 0]);
        if (['fixed', 'pin'].includes(support.kind) || support.kind === 'custom' && support.fixY) blockedDirections.push([0, 1, 0]);
        if (['fixed', 'guided'].includes(support.kind) || support.kind === 'custom' && support.fixRotation) blockedDirections.push([0, 0, 1]);
        if (['roller', 'guided'].includes(support.kind)) blockedDirections.push([Math.cos(support.angle * Math.PI / 180), Math.sin(support.angle * Math.PI / 180), 0]);
        for (const direction of blockedDirections) constraints.push({ support, index, direction,
            row: Array.from({ length: dofs }, (_, column) => direction.reduce((sum, value, i) => sum + value * mapping[i][column], 0)) });
    }
    function orthogonalize(candidate: number[], vectors: number[][]): number[] | null {
        let remainder = [...candidate];
        // Reorthogonalization limits cancellation for coincident constraints.
        for (let pass = 0; pass < 2; pass++) for (const vector of vectors) {
            const projection = dot(remainder, vector);
            remainder = remainder.map((value, i) => value - projection * vector[i]);
        }
        const norm = Math.hypot(...remainder);
        return norm > tolerance ? remainder.map(value => value / norm) : null;
    }
    const blocked: number[][] = [], basis: number[][] = [];
    for (const constraint of constraints) {
        const vector = orthogonalize(constraint.row, blocked);
        if (vector) blocked.push(vector);
    }
    const restrained = blocked.length;
    for (let column = 0; column < dofs; column++) {
        const candidate = Array(dofs).fill(0); candidate[column] = 1;
        const vector = orthogonalize(candidate, [...blocked, ...basis]);
        if (vector) basis.push(vector);
    }
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
    // 4. Recover section forces from equilibrium, then integrate them. The load
    // particular solution is retained, giving exact polynomial deflections for
    // each prismatic segment with linear distributed loading.
    const connectionResults: NonNullable<Analysis['connections']> = [];
    const elements = segments.map(segment => {
        const { i, j, length: L, c, s, member } = segment;
        const local = multiplyVector(segment.mapping!, displacement);
        const actions = multiplyVector(segment.stiffness, local).map((v, k) => v - segment.equivalent[k]);
        for (const flexible of flexibleEnds.filter(item => item.member.id === member.id)) {
            if (flexible.end === 'a' && segment.t0 > tolerance || flexible.end === 'b' && segment.t1 < 1 - tolerance) continue;
            const slips = flexible.indices.map(index => index < 0 ? 0 : displacement[index]);
            const offset = flexible.end === 'a' ? 0 : 3;
            connectionResults.push({ node: member[flexible.end], member: member.id, end: flexible.end,
                axialSlip: slips[0], transverseSlip: slips[1], relativeRotation: slips[2],
                axialForce: -actions[offset], transverseForce: -actions[offset + 1], moment: -actions[offset + 2] });
        }
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
    // Constraint multipliers recover physical ground actions. Dependent,
    // coincident constraints have a unique combined reaction, not a unique split.
    const multipliers = reduce(constraints.map(a => constraints.map(b => dot(a.row, b.row))), constraints.map(item => dot(item.row, imbalance))).solution;
    const reactions = [...supportGroups].map(([index, supports]) => {
        const components = [0, 0, 0];
        constraints.forEach((constraint, i) => {
            if (constraint.index === index) constraint.direction.forEach((value, j) => { components[j] += value * multipliers[i]; });
        });
        return { ...points[index], fx: components[0], fy: components[1], mz: components[2], supports: supports.map(s => s.id) };
    });
    const degree = 3 * segments.length + springCount + restrained - dofs;
    return { status: 'stable', message: degree === 0 ? 'Stable · statically determinate' : `Stable · statically indeterminate (degree ${degree})`, degree, elements, residual,
        reactions, connections: connectionResults };
}
/** Splitting a drawn member creates a rigid joint and remaps attached objects. */
export function splitMember(model: Model, memberId: string, t: number, nodeId: string): string {
    const member = model.members.find(m => m.id === memberId)!;
    if (t < 1e-6)
        return member.a;
    if (t > 1 - 1e-6)
        return member.b;
    const point = position(model, memberId, t);
    // Insert the new station between the existing end labels. IDs remain stable
    // while the displayed alphabetical sequence follows the subdivided member.
    const insertion = Math.min(model.nodes.findIndex(node => node.id === member.a), model.nodes.findIndex(node => node.id === member.b)) + 1;
    model.nodes.splice(insertion, 0, { id: nodeId, ...point });
    const secondId = `${memberId}-${nodeId}`;
    const second: Member = { ...member, id: secondId, a: nodeId, connectionA: undefined };
    const formerEnd = model.nodes.find(node => node.id === member.b)!;
    if (formerEnd.referenceMember === member.id) formerEnd.referenceMember = secondId;
    member.b = nodeId;
    member.connectionB = undefined;
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
    if (['hinge', 'semi-rigid', 'sliding'].includes(name)) {
        model.nodes = [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 4, y: 0, joint: name === 'hinge' ? 'pinned' : name === 'semi-rigid' ? 'semi-rigid' : 'custom', rotationStiffness: 10000 }, { id: 'C', x: 8, y: 0 }];
        model.members = [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }, { id: 'BC', a: 'B', b: 'C', EA: 2000000, EI: 20000 }];
        model.supports = [{ id: 'S1', member: 'AB', t: 0, kind: 'fixed', angle: 90 }];
        if (name !== 'semi-rigid') model.supports.push({ id: 'S2', member: 'BC', t: 1, kind: name === 'sliding' ? 'fixed' : 'roller', angle: 90 });
        if (name === 'sliding') model.members[1].connectionA = { axial: 'free', transverse: 'rigid', rotation: 'free' };
        model.loads = [{ id: 'P1', member: 'BC', kind: 'force', t: name === 'semi-rigid' ? 1 : 0.5, end: 1, fx: 0, fy: -20, mz: 0, qEnd: -5 }];
    }
    if (name === 'mixed') {
        model.nodes = [{ id: 'A', x: 0, y: 3 }, { id: 'B', x: 4, y: 3, joint: 'custom' }, { id: 'C', x: 8, y: 3 }, { id: 'D', x: 4, y: 0 }];
        model.members = [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }, { id: 'BC', a: 'B', b: 'C', EA: 2000000, EI: 20000 }, { id: 'BD', a: 'B', b: 'D', EA: 2000000, EI: 20000, connectionA: { axial: 'rigid', transverse: 'rigid', rotation: 'free' } }];
        model.supports = [{ id: 'S1', member: 'AB', t: 0, kind: 'pin', angle: 90 }, { id: 'S2', member: 'BC', t: 1, kind: 'roller', angle: 90 }, { id: 'S3', member: 'BD', t: 1, kind: 'pin', angle: 90 }];
        model.loads = [{ id: 'P1', member: 'BC', kind: 'force', t: 0.5, end: 1, fx: 0, fy: -20, mz: 0, qEnd: -5 }];
    }
    return model;
}
