/** Course labels and member-end connections shared by the canvas and inspector. */
import { endConnection, nodeLabels } from './engine.js';
import type { Member, Model, Point } from './engine.js';

export interface Selection {
    type: string;
    id: string;
}

export function memberLabel(model: Model, member: Member): string {
    const labels = nodeLabels(model);
    return `${labels.get(member.a)}–${labels.get(member.b)}`;
}

export function jointConnections(model: Model, node: Point) {
    return model.members
        .filter(member => member.a === node.id || member.b === node.id)
        .map(member => {
            const end = member.a === node.id ? 'a' : 'b';
            return { member, end: end as 'a' | 'b', rule: endConnection(model, member, end) };
        });
}
