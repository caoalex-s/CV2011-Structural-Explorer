/** Applicability of the parameterized LessonBeam equilibrium and section rules. */
import type { Model } from './engine.js';
import { loadLabels, loadLabelLatex } from './load-labels.js';

export function pointForceRules(model: Model, section: number) {
    if (model.nodes.length !== 2 || model.members.length !== 1 || model.supports.length !== 2 || model.loads.length !== 1) return null;
    const member = model.members[0], load = model.loads[0];
    const left = model.nodes.find(node => node.id === member.a), right = model.nodes.find(node => node.id === member.b);
    if (!left || !right || model.nodes[0] !== left || model.nodes[1] !== right ||
        ![left.x, left.y, right.x, right.y].every(Number.isFinite) || left.y !== right.y || right.x <= left.x ||
        model.nodes.some(node => node.joint && node.joint !== 'rigid') || member.connectionA || member.connectionB) return null;
    const supports = [...model.supports].sort((a, b) => a.t - b.t);
    if (supports.some(support => support.member !== member.id) || supports[0].t !== 0 || supports[1].t !== 1 ||
        !['pin,roller', 'roller,pin'].includes(supports.map(support => support.kind).join(',')) ||
        supports.some(support => support.kind === 'roller' && support.angle !== 90)) return null;
    if (load.member !== member.id || load.kind !== 'force' || load.fx !== 0 || !Number.isFinite(load.fy) ||
        !Number.isFinite(load.t) || load.t < 0 || load.t > 1 || !Number.isFinite(section) || section < 0 || section > 1) return null;
    const L = right.x - left.x, a = load.t * L, x = section * L, P = -load.fy;
    const leftReaction = P * (L - a) / L, rightReaction = P * a / L;
    // The right endpoint uses the left-hand limit, excluding an action at the cut.
    const after = section > load.t || (section === load.t && section < 1);
    return { L, a, x, P, leftReaction, rightReaction, after,
        shear: after ? leftReaction - P : leftReaction,
        moment: leftReaction * x - (after ? P * (x - a) : 0),
        label: loadLabelLatex(loadLabels(model).get(load.id)!), maximum: P >= 0 };
}
