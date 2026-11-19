/** Reduced interval proposal for shared translations and independently rotating
 * member ends. The checker reconstructs the ownership map from the source. */
import { endConnection,            } from './engine.js';
import { parseEvidenceModel,                    } from './model-evidence.js';
import { frameLimits } from './frame-candidate.js';
import { compileIntervalFrame } from './frame-interval-model.js';
import { IntervalArithmetic } from './frame-interval.js';
import { pointBasis } from './frame-interval-basis.js';
import { intervalDot } from './frame-interval-solve.js';
import { zero, one } from './frame-rational.js';

export function compileInclinedRelease(arithmetic                    , input         , query               ) {
    if (input && typeof input === 'object') {
        const outer = input                           ;
        const raw = (outer.version === 2 ? outer.model : outer)                                       ;
        for (const key of ['members', 'nodes', 'supports', 'loads']         ) {
            const items = raw?.[key];
            if (Array.isArray(items) && items.length > frameLimits[key]) throw Error(`Limit: too many ${key}.`);
        }
    }
    const model = parseEvidenceModel(input);
    const expanded        = { ...model,
        nodes: model.nodes.map(node => ({ ...node, joint: 'rigid', referenceMember: undefined })),
        members: model.members.map(({ connectionA, connectionB, ...member }) => ({ ...member })) };
    const parent = model.nodes.map((_, index) => index);
    for (const node of model.nodes) if (node.joint === 'semi-rigid') throw Error('Unsupported: rotational springs.');
    for (const [index, member] of model.members.entries()) {
        for (const end of ['a', 'b']         ) {
            const explicit = end === 'a' ? member.connectionA : member.connectionB;
            if (explicit && (explicit.axial !== 'rigid' || explicit.transverse !== 'rigid' || typeof explicit.rotation === 'number'))
                throw Error('Unsupported: only rotational releases are supported.');
            if (endConnection(model, member, end).rotation !== 'free') continue;
            const node = model.nodes.findIndex(item => item.id === member[end]);
            let id = 'release-' + expanded.nodes.length;
            while (expanded.nodes.some(item => item.id === id)) id += '_';
            expanded.members[index][end] = id;
            expanded.nodes.push({ ...expanded.nodes[node], id });
            parent.push(node);
        }
    }
    if (parent.length === model.nodes.length) throw Error('Unsupported: draw at least one released end.');
    const mesh = compileIntervalFrame(arithmetic, expanded, query);
    for (let i = parent.length; i < mesh.points.length; i++) parent.push(i);
    const z = arithmetic.bounds(zero), u = arithmetic.bounds(one);
    // Columns for translations belong to the shared joint. A support moment
    // or applied couple belongs to the particular end selected in the drawing.
    const columns = mesh.points.flatMap((_, point) => {
        const supports = model.supports.filter((_, i) => parent[mesh.supportPoints[i]] === point);
        const translations = point === parent[point] ? pointBasis(arithmetic, supports).columns.filter(c => c.coordinate !== 'rotation') : [];
        const rotationFixed = model.supports.some((support, i) => support.kind === 'fixed' && mesh.supportPoints[i] === point);
        const columns = translations.map(column => ({ point, rotation: false, values: column.components }));
        if (!rotationFixed) columns.push({ point, rotation: true, values: [z, z, u] });
        return columns;
    });
    if (columns.length > frameLimits.coordinates) throw Error('Limit: too many independent coordinates.');
    const basis = mesh.force.map((_, row) => columns.map(column => {
        const point = Math.floor(row / 3), component = row % 3;
        const owner = component === 2 ? point : parent[point];
        return column.point === owner ? column.values[component] : z;
    }));
    const transpose = columns.map((_, j) => basis.map(row => row[j]));
    const matrixTimesBasis = transpose.map(column => mesh.stiffness.map(row => intervalDot(arithmetic, row, column)));
    const reduced = transpose.map(column => matrixTimesBasis.map(right => intervalDot(arithmetic, column, right)));
    const reducedForce = transpose.map(column => intervalDot(arithmetic, column, mesh.force));
    return { model, reduced, reducedForce, coordinates: columns };
}
