/** Course labels and member-end connections shared by the canvas and inspector. */
import { endConnection, nodeLabels } from './engine.js';
import type { Member, Model, Point } from './engine.js';

export interface Selection {
    type: string;
    id: string;
}

export function memberLabel(model: Model, member: Member): string {
    const labels = nodeLabels(model);
    const start = labels.get(member.a) ?? '?';
    const end = labels.get(member.b) ?? '?';
    // Separate multi-letter joint names so the two endpoints are identifiable.
    return start.length === 1 && end.length === 1 ? start + end : start + ' ' + end;
}

/** Reaction notation for a named joint, with generic symbols for other points. */
export function reactionSymbols(joint?: string): [string, string, string] {
    return joint ? [`${joint}_x`, `${joint}_y`, `M_{${joint}}`] : ['R_x', 'R_y', 'M_z'];
}

export function jointConnections(model: Model, node: Point) {
    return model.members
        .filter(member => member.a === node.id || member.b === node.id)
        .map(member => {
            const end = member.a === node.id ? 'a' : 'b';
            return { member, end: end as 'a' | 'b', rule: endConnection(model, member, end) };
        });
}
