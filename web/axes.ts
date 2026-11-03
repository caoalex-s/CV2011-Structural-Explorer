/** Fixed global axes and the selected member's right-handed local axes. */
import type { Model } from './engine.js';

export function memberBasis(model: Model, memberId: string): { cosine: number; sine: number } | undefined {
    const member = model.members.find(item => item.id === memberId);
    const start = model.nodes.find(node => node.id === member?.a);
    const end = model.nodes.find(node => node.id === member?.b);
    if (!start || !end) return undefined;
    const length = Math.hypot(end.x - start.x, end.y - start.y);
    if (length === 0) return undefined;
    return { cosine: (end.x - start.x) / length, sine: (end.y - start.y) / length };
}

function axesSvg(cosine: number, sine: number, id: string, labels: [string, string]): string {
    // Screen y points down; physical y points up. Keep the labels upright.
    const endX = { x: 45 + 25*cosine, y: 45 - 25*sine };
    const endY = { x: 45 - 25*sine, y: 45 - 25*cosine };
    return `<svg viewBox="0 0 90 90" aria-hidden="true"><defs><marker id="${id}" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" orient="auto"><path d="M0 0 L8 4 L0 8 Z" fill="currentColor"/></marker></defs><path d="M45 45 L${endX.x} ${endX.y} M45 45 L${endY.x} ${endY.y}" fill="none" stroke="currentColor" stroke-width="1.6" marker-end="url(#${id})"/><text x="${45+37*cosine}" y="${49-37*sine}" text-anchor="middle">${labels[0]}</text><text x="${45-37*sine}" y="${49-37*cosine}" text-anchor="middle">${labels[1]}</text></svg>`;
}

export function workspaceConventions(model: Model, memberId: string): string {
    const basis = memberBasis(model, memberId);
    return `<div class="axis-item">${axesSvg(1, 0, 'global-axis-arrow', ['x', 'y'])}<span><b>Global axes</b><br>+x right · +y up<br>Readouts: +v upward · +θ ↺</span></div>
        <div class="axis-item">${basis ? axesSvg(basis.cosine, basis.sine, 'local-axis-arrow', ['x', 'y']) : ''}<span><b>Member axes</b><br>${basis ? 'Selected member: x start → end' : 'Select a member'}<br>y: 90° counterclockwise from x</span></div>
        <div class="axis-item cut-convention"><span><b>Positive cut actions</b><br>Right face of the retained start portion:<br>N along +x · V along −y · M ↺<br><small>Moment plotting side does not change these signs.</small></span></div>`;
}
