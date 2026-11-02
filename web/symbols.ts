/** SVG equivalents of the course's cv2011figures helpers. World y is up;
 * SVG y is down. Labels may move, but action origins and lines never do. */
export const courseColors = { member: '#16334A', force: '#2F6F73', reaction: '#C9A227', ink: '#202020', muted: '#657177' };
const escapeText = (value: string) => value.replace(/[&<>"']/g, character => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[character]!));

export function forceGeometry(x: number, y: number, fx: number, fy: number, length = 60, gap = 5) {
    const magnitude = Math.hypot(fx, fy);
    if (magnitude < 1e-12) return null;
    const ux = fx / magnitude, uy = -fy / magnitude;
    return { origin: { x, y }, tip: { x: x - gap * ux, y: y - gap * uy }, tail: { x: x - (gap + length) * ux, y: y - (gap + length) * uy }, ux, uy };
}
function arrowHead(x: number, y: number, ux: number, uy: number, color: string): string {
    return `<path d="M ${x} ${y} L ${x - 10 * ux + 3.5 * uy} ${y - 10 * uy - 3.5 * ux} L ${x - 8 * ux} ${y - 8 * uy} L ${x - 10 * ux - 3.5 * uy} ${y - 10 * uy + 3.5 * ux} Z" fill="${color}"/>`;
}
export function forceSymbol(x: number, y: number, fx: number, fy: number, color: string, label = '', length = 60, gap = 5): string {
    const geometry = forceGeometry(x, y, fx, fy, length, gap);
    if (!geometry) return '';
    const { tip, tail, ux, uy } = geometry;
    const leader = gap > 8 ? `<path d="M ${tip.x} ${tip.y} L ${x} ${y}" stroke="${color}" stroke-width="0.8" stroke-dasharray="2 3" opacity=".65"/>` : '';
    // Keep the hit region on the actual arrow for forces in every direction.
    return `<g data-vector="force" data-origin-x="${x}" data-origin-y="${y}">${leader}<path class="hit" d="M ${tail.x} ${tail.y} L ${tip.x} ${tip.y}"/><path d="M ${tail.x} ${tail.y} L ${tip.x} ${tip.y}" stroke="${color}" stroke-width="1.8" fill="none"/>${arrowHead(tip.x, tip.y, ux, uy, color)}${label ? `<text x="${tail.x + 8}" y="${tail.y - 9}" class="svg-label" style="fill:${color}">${escapeText(label)}</text>` : ''}</g>`;
}
export function momentGeometry(x: number, y: number, moment: number, radius = 25) {
    const positive = moment >= 0, startAngle = positive ? -Math.PI / 4 : 5 * Math.PI / 4;
    const endAngle = positive ? 5 * Math.PI / 4 : -Math.PI / 4;
    const sense = positive ? 1 : -1;
    return { center: { x, y }, radius,
        start: { x: x + radius * Math.cos(startAngle), y: y - radius * Math.sin(startAngle) },
        end: { x: x + radius * Math.cos(endAngle), y: y - radius * Math.sin(endAngle) },
        tangent: { x: -sense * Math.sin(endAngle), y: -sense * Math.cos(endAngle) }, sweep: positive ? 0 : 1 };
}
export function momentSymbol(x: number, y: number, moment: number, color: string, label = '', radius = 25): string {
    if (Math.abs(moment) < 1e-12) return '';
    const { start, end, tangent, sweep } = momentGeometry(x, y, moment, radius);
    const arc = `M ${start.x} ${start.y} A ${radius} ${radius} 0 1 ${sweep} ${end.x} ${end.y}`;
    return `<g data-vector="moment" data-origin-x="${x}" data-origin-y="${y}"><path class="hit" d="${arc}"/><path d="${arc}" fill="none" stroke="${color}" stroke-width="1.8"/>${arrowHead(end.x, end.y, tangent.x, tangent.y, color)}${label ? `<text x="${x}" y="${y - radius - 10}" text-anchor="middle" class="svg-label" style="fill:${color}">${escapeText(label)}</text>` : ''}</g>`;
}
/** A spiral marks a rotational spring. Its centre is the joint itself. */
export function rotationalSpring(x: number, y: number, color = courseColors.member): string {
    const path = Array.from({ length: 65 }, (_, i) => {
        const angle = i / 64 * Math.PI * 3.5, radius = 3 + i / 64 * 9;
        return `${i ? 'L' : 'M'} ${x + radius * Math.cos(angle)} ${y - radius * Math.sin(angle)}`;
    }).join(' ');
    return `<circle cx="${x}" cy="${y}" r="13" fill="white"/><path d="${path}" fill="none" stroke="${color}" stroke-width="1.5"/>`;
}
/** Stanli support 1 (pin), support 2 (sliding bearing), and fixed wall.
 * All symbols start at the exact insertion point. */
export function supportShape(kind: string): string {
    const hatching = '<path d="M -20 21 l -5 6 M -10 21 l -5 6 M 0 21 l -5 6 M 10 21 l -5 6 M 20 21 l -5 6"/>';
    if (kind === 'fixed') return '<path d="M 0 -24 V 24 M 0 -23 l -9 9 M 0 -13 l -9 9 M 0 -3 l -9 9 M 0 7 l -9 9 M 0 17 l -9 9"/>';
    if (kind === 'pin') return `<path d="M 0 0 L -14 21 H 14 Z" fill="white"/><path d="M -21 21 H 21"/>${hatching}`;
    if (kind === 'roller') return `<path d="M 0 0 L -14 17.5 H 14 Z" fill="white"/><path d="M -21 17.5 H 21 M -21 21 H 21"/>${hatching}`;
    if (kind === 'guided') return `<path d="M -9 0 H 9 V 15 H -9 Z M 0 0 V 15 M -21 17.5 H 21 M -21 21 H 21" fill="white"/>${hatching}`;
    return '<path d="M 0 0 V 15 M -12 15 H 12 V 34 H -12 Z" fill="white"/>';
}
