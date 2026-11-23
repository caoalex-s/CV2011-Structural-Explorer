import type { Drawing } from './ideal-truss.js';
import type { CheckedSection, Query } from './week04-section.js';
type Point = {
    x: number;
    y: number;
};
const sx = (x: number) => 88 + x * 78, sy = (y: number) => 80 - y * 78;
function line(a: Point, b: Point, style: string) {
    return `<line x1="${sx(a.x)}" y1="${sy(a.y)}" x2="${sx(b.x)}" y2="${sy(b.y)}" ${style}/>`;
}
function text(x: number, y: number, label: string, anchor = 'start') {
    return `<text x="${x}" y="${y}" text-anchor="${anchor}" font-size="14">${label}</text>`;
}
function arrow(origin: Point, dx: number, dy: number, label: string, kind: string, name: string) {
    if (!dx && !dy)
        return '';
    const length = Math.hypot(dx, dy), ux = dx / length, uy = -dy / length;
    const x = sx(origin.x), y = sy(origin.y), ex = x + ux * 38, ey = y + uy * 38;
    const color = kind === 'cut' ? '#155e75' : '#9c4318';
    return `<g data-action="${name}" data-direction-x="${dx}" data-direction-y="${dy}">
      <line x1="${x}" y1="${y}" x2="${ex}" y2="${ey}" stroke="${color}" stroke-width="2.5"/>
      <path fill="${color}" d="M${ex},${ey} l${-9 * ux - 4 * uy},${-9 * uy + 4 * ux} l${8 * uy},${-8 * ux} z"/>
      ${text(ex + (ux < 0 ? -5 : 5), ey + (uy > 0 ? 12 : -5), label, ux < 0 ? 'end' : 'start')}</g>`;
}
export function diagram(d: Drawing, q: Query, section?: CheckedSection) {
    const byId = new Map(d.joints.map(j => [j.id, j]));
    const retained = (j: Point) => !section || (q.side === 'left' ? j.x < q.cut : j.x > q.cut);
    const bars: string[] = [], actions: string[] = [];
    const terms = new Map(section?.terms.map(t => [t.name, t]));
    const p = -byId.get('A')!.fy;
    for (const [a, b] of d.bars) {
        let first: Point = byId.get(a)!, last: Point = byId.get(b)!;
        if (!retained(first) && !retained(last))
            continue;
        if (!retained(first))
            [first, last] = [last, first];
        if (!retained(last)) {
            const end = { x: q.cut, y: first.y + (last.y - first.y) * (q.cut - first.x) / (last.x - first.x) };
            const t = terms.get(a + b)!;
            actions.push(arrow(end, t.x, t.y, 'F' + a + b, 'cut', a + b));
            last = end;
        }
        bars.push(line(first, last, 'stroke="#334e58" stroke-width="4"'));
    }
    const joints = d.joints.filter(retained).map(j => {
        const x = sx(j.x), y = sy(j.y);
        const label = text(x + (j.id === 'D' ? 10 : -9), y + (j.y < 0 ? 20 : -12), j.id, j.id === 'D' ? 'start' : 'end');
        const support = section ? '' : j.support === 'pin' ? `<path d="M${x},${y} l16,-10 v20 z" fill="#dce8e9" stroke="#234853"/>` :
            j.support === 'roller' ? `<g stroke="#234853" fill="#dce8e9"><path d="M${x},${y} l13,-9 v18 z"/><circle cx="${x + 17}" cy="${y - 5}" r="3"/><circle cx="${x + 17}" cy="${y + 5}" r="3"/><path d="M${x + 21},${y - 12}v24"/></g>` : '';
        return support + `<circle cx="${x}" cy="${y}" r="4" fill="white" stroke="#203d49" stroke-width="2"/>` + label;
    }).join('');
    const a = byId.get('A')!;
    if (retained(a))
        actions.push(arrow(a, 0, -p, Math.abs(p) + ' kN', 'external', 'P'));
    if (section && q.side === 'right') {
        const { Dx, Dy, Ex } = section.reactions;
        actions.push(arrow(byId.get('D')!, Dx, 0, 'Dₓ ' + Math.abs(Dx) + ' kN', 'external', 'Dx'), arrow(byId.get('D')!, 0, Dy, 'Dᵧ ' + Math.abs(Dy) + ' kN', 'external', 'Dy'), arrow(byId.get('E')!, Ex, 0, 'Eₓ ' + Math.abs(Ex) + ' kN', 'external', 'Ex'));
    }
    const centre = byId.get(q.centre)!;
    const pivot = `<circle cx="${sx(centre.x)}" cy="${sy(centre.y)}" r="9" fill="none" stroke="#985a1f" stroke-width="1.5"/>` +
        (section && !retained(centre) ? text(sx(centre.x), sy(centre.y) + 25, q.centre, 'middle') : '');
    const cut = line({ x: q.cut, y: .6 }, { x: q.cut, y: -2.55 }, 'stroke="#9d5225" stroke-dasharray="6 5" stroke-width="2"');
    const dimensions = section ? '' : `<g fill="#415762">${[0, 2, 4].map(x => line({ x, y: -2.88 }, { x: x + 2, y: -2.88 }, 'stroke="#809699"') + text(sx(x + 1), sy(-2.88) - 5, '2 m', 'middle')).join('')}
        ${line({ x: 6.9, y: 0 }, { x: 6.9, y: -2 }, 'stroke="#809699"')}${text(sx(6.9) + 4, sy(-1), '2 m')}</g>`;
    return `<svg id="${section ? 'section-fbd' : 'section-drawing'}" viewBox="0 0 680 335" role="img" aria-label="${section ? q.side + ' free body with cut forces assumed tensile' : 'Seven-joint truss with selected vertical cut'}">${dimensions}${cut}${text(sx(q.cut), sy(.6) - 7, 'a–a', 'middle')}${bars.join('')}${pivot}${joints}${actions.join('')}</svg>`;
}
