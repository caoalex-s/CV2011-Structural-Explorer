/** Exact candidate assembly for cardinal frames with rotational end releases. */
import { endConnection, type Model } from './engine.js';
import { compileFrame, frameLimits, type CompiledFrame } from './frame-candidate.js';
import { parseEvidenceModel, type EvidenceQuery } from './model-evidence.js';
import { add, binary64, equal, mul, one, zero } from './frame-rational.js';

export interface ReleasedRotation { member: number; end: 'a' | 'b'; node: number; coordinate: number }
export interface HingeFrame extends CompiledFrame { released: ReleasedRotation[] }

/** Each point's first rotation belongs to its reference member. Every other
 * freely rotating end gets one absolute rotation. Point translations remain
 * shared. The untrusted candidate uses the same element physics as the rigid
 * solver, with these physical coordinates assigned before assembly. */
export function compileHingeFrame(input: unknown, query: EvidenceQuery): HingeFrame {
    if (input && typeof input === 'object') {
        const outer = input as Record<string, unknown>;
        const source = (outer.version === 2 ? outer.model : outer) as Record<string, unknown> | undefined;
        for (const key of ['members', 'nodes', 'supports', 'loads'] as const) {
            const items = source?.[key];
            if (Array.isArray(items) && items.length > frameLimits[key]) throw Error(`Limit: too many ${key}.`);
        }
    }
    const model = parseEvidenceModel(input);
    if (model.nodes.some(node => node.joint === 'semi-rigid'))
        throw Error('Unsupported: rotational springs.');
    // Only the cut geometry, segment matrices and consistent segment loads
    // from this pass are reused. Reassemble all loads and restraints below.
    const geometry: Model = { ...model, nodes: model.nodes.map(node => ({ ...node, joint: 'rigid' })),
        members: model.members.map(({ connectionA, connectionB, ...member }) => member) };
    const mesh = compileFrame(geometry, query);
    const released: ReleasedRotation[] = [];
    for (const [index, member] of model.members.entries()) {
        for (const end of ['a', 'b'] as const) {
            const rule = endConnection(model, member, end);
            if (rule.axial !== 'rigid' || rule.transverse !== 'rigid' || typeof rule.rotation === 'number')
                throw Error('Unsupported: this checker requires shared translations and rigid or free rotation.');
            if (rule.rotation === 'free') {
                const node = model.nodes.findIndex(item => item.id === member[end]);
                released.push({ member: index, end, node, coordinate: 3 * mesh.points.length + released.length });
            }
        }
    }
    if (!released.length) throw Error('Unsupported: no active rotational release.');
    const count = 3 * mesh.points.length + released.length;
    if (count > frameLimits.coordinates) throw Error('Limit: too many motion coordinates including released ends.');
    function rotation(member: number, end: 'a' | 'b' | undefined, point: number): number {
        return released.find(item => item.member === member && item.end === end)?.coordinate ?? 3 * point + 2;
    }
    const segments = mesh.segments.map(segment => {
        const indices = [...segment.indices];
        indices[2] = rotation(segment.member, equal(segment.from, zero) ? 'a' : undefined, segment.start);
        indices[5] = rotation(segment.member, equal(segment.to, one) ? 'b' : undefined, segment.end);
        return { ...segment, indices };
    });
    const stiffness = Array.from({ length: count }, () => Array(count).fill(zero) as typeof mesh.force);
    const force = Array(count).fill(zero) as typeof mesh.force;
    for (const segment of segments) {
        segment.indices.forEach((row, i) => {
            force[row] = add(force[row], mul(segment.signs[i], segment.force[i]));
            segment.indices.forEach((column, j) => {
                const coefficient = mul(segment.stiffness[i][j], mul(segment.signs[i], segment.signs[j]));
                stiffness[row][column] = add(stiffness[row][column], coefficient);
            });
        });
    }
    function coordinates(memberId: string, t: number) {
        const member = model.members.findIndex(item => item.id === memberId);
        const parameter = binary64(t);
        const boundary = segments.find(segment => segment.member === member && equal(segment.from, parameter));
        const point = boundary?.start ?? segments.find(segment => segment.member === member && equal(segment.to, parameter))?.end;
        if (point === undefined) throw Error('Missing source load or support cut.');
        return [3 * point, 3 * point + 1, rotation(member, t === 0 ? 'a' : t === 1 ? 'b' : undefined, point)];
    }
    for (const load of model.loads) {
        if (load.kind === 'distributed') continue;
        const [x, y, angle] = coordinates(load.member, load.t);
        if (load.kind === 'moment') force[angle] = add(force[angle], binary64(load.mz));
        else {
            force[x] = add(force[x], binary64(load.fx));
            force[y] = add(force[y], binary64(load.fy));
        }
    }
    const blocked: boolean[] = Array(count).fill(false);
    for (const support of model.supports) {
        const [x, y, angle] = coordinates(support.member, support.t);
        if (support.kind === 'roller') blocked[support.angle % 180 === 0 ? x : y] = true;
        else {
            blocked[x] = blocked[y] = true;
            if (support.kind === 'fixed') blocked[angle] = true;
        }
    }
    const structuralKey = JSON.stringify([mesh.structuralKey, model.nodes, model.members, released]);
    return { ...mesh, model, released, segments, stiffness, force, blocked,
        free: blocked.flatMap((fixed, index) => fixed ? [] : [index]), structuralKey,
        boundaryKey: JSON.stringify([structuralKey, blocked]) };
}
