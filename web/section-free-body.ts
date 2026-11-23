import { type Analysis, type Model, type Sample } from './engine.js';
import { loadLabels } from './load-labels.js';
import { memberLabel } from './model-view.js';
import { sampleSection } from './responses.js';
import { courseColors, forceSymbol, momentSymbol } from './symbols.js';
import { escapeHtml, formatNumber } from './ui.js';

type Side = 'left' | 'right';

// Draw in member axes so the same sign convention applies to inclined members.
// At the original ends the resultant includes all connections, supports and
// applied end loads. Interior actions are shown individually.
export function sectionFreeBody(model: Model, analysis: Analysis, memberId: string,
    t: number, side: Side, cut: Sample) {
    const member = model.members.find(m => m.id === memberId)!;
    const start = model.nodes.find(n => n.id === member.a)!;
    const end = model.nodes.find(n => n.id === member.b)!;
    const length = Math.hypot(end.x - start.x, end.y - start.y);
    const c = (end.x - start.x) / length, s = (end.y - start.y) / length;
    const retainRight = t === 0;
    const extent = retainRight ? 1 : t;
    const x = (station: number) => 76 + 420 * station / extent;
    const y = 90;
    const labels = loadLabels(model);
    const rows: string[] = [];
    const unitForce = (v: number) => Math.abs(v) < 1e-7 ? 0 : v;
    function action(station: number, fx: number, fy: number, moment: number, name: string, color: string, symbol = '', cutFace = false) {
        const X = unitForce(fx), Y = unitForce(fy), C = unitForce(moment);
        rows.push(`<li>${escapeHtml(name)} · x = ${formatNumber(station * length)} m · (${formatNumber(X)}, ${formatNumber(Y)}) kN · ${formatNumber(C)} kN·m</li>`);
        // Concentric arcs distinguish an applied couple from the cut moment.
        const force = cutFace
            ? forceSymbol(x(station), y, X, 0, color, 'N', 27, 0)
                + forceSymbol(x(station), y, 0, Y, color, 'V', 27, 0)
            : forceSymbol(x(station), y, X, Y, color, symbol, 43, 0);
        return force + momentSymbol(x(station), y, C, color, cutFace ? 'M' : symbol, cutFace ? 17 : 31, 0, !cutFace);
    }
    const opposite = retainRight ? 1 : 0;
    const endValues = sampleSection(analysis, memberId, opposite, retainRight ? 'left' : 'right', model);
    if (!endValues) return '<p>The numerical mesh combines actions near the member end. Its end resultant cannot be separated for this free body.</p>';
    const sign = retainRight ? 1 : -1;
    let arrows = action(opposite, sign * endValues.N, -sign * endValues.V, sign * endValues.M,
        'Net member-end action', courseColors.reaction);
    const includes = (station: number) => station > 0 && station < 1 &&
        (retainRight || station < t || station === t && side === 'right');
    for (const load of model.loads.filter(load => load.member === memberId)) {
        const label = labels.get(load.id)!;
        let drawing = '';
        if (load.kind === 'distributed') {
            const stop = Math.min(extent, load.end);
            if (stop <= load.t) continue;
            const intensity = (station: number) => load.fy + (load.qEnd - load.fy) * (station - load.t) / (load.end - load.t);
            const maximum = Math.max(Math.abs(intensity(load.t)), Math.abs(intensity(stop)), 1e-12);
            for (let i = 0; i <= 5; i++) {
                const station = load.t + (stop - load.t) * i / 5;
                const q = intensity(station);
                drawing += forceSymbol(x(station), y, s*q, c*q, courseColors.force, '', 32*Math.abs(q)/maximum, 0);
            }
            rows.push(`<li>${escapeHtml(label)} · x = ${formatNumber(load.t*length)} to ${formatNumber(stop*length)} m · global vertical intensity ${formatNumber(intensity(load.t))} to ${formatNumber(intensity(stop))} kN/m</li>`);
        } else if (includes(load.t)) {
            drawing = action(load.t, load.kind === 'force' ? c*load.fx+s*load.fy : 0,
                load.kind === 'force' ? -s*load.fx+c*load.fy : 0, load.kind === 'moment' ? load.mz : 0, label, courseColors.force, label);
        } else continue;
        arrows += `<g data-load-id="${escapeHtml(load.id)}">${drawing}</g>`;
    }
    for (const reaction of analysis.reactions) {
        const support = model.supports.find(p => p.member === memberId && reaction.supports.includes(p.id) && includes(p.t));
        if (support) arrows += action(support.t, c*reaction.fx+s*reaction.fy, -s*reaction.fx+c*reaction.fy,
            reaction.mz, 'Support reaction', courseColors.reaction);
    }
    arrows += action(t, -sign*cut.N, sign*cut.V, -sign*cut.M, 'Cut action', courseColors.member, '', true);
    const station = formatNumber(t*length);
    const caption = `Member ${memberLabel(model,member)} · x = ${station} m · just ${side}`;
    return `<figure><figcaption>${caption}</figcaption><svg id="section-fbd" viewBox="0 0 580 185" role="img"
        data-member="${escapeHtml(memberId)}" data-parameter="${t}" data-side="${side}" aria-label="${caption}">
        <title>${caption}. Retained ${retainRight ? 'end' : 'start'} portion in member axes.</title>
        <path d="M76 ${y}H496" stroke="${courseColors.member}" stroke-width="4"/>
        <path d="M${x(t)} 44v90" stroke="#96513b" stroke-dasharray="4 4"/>
        ${arrows}<text x="${x(opposite)}" y="172" text-anchor="middle">Member end</text>
        <text x="${x(t)}" y="172" text-anchor="middle">Cut</text></svg></figure>
        <p class="fbd-values">N = ${formatNumber(cut.N)} kN · V = ${formatNumber(cut.V)} kN · M = ${formatNumber(cut.M)} kN·m</p>
        <p class="small">The free body retains the ${retainRight ? 'end' : 'start'} portion. Local x runs from the first joint to the second. Arrows show the resultant actions on this portion.</p>
        <details><summary>Forces and couples on the free body</summary><p>Force components are in member axes. Couples are positive counterclockwise.</p><ul>${rows.join('')}</ul></details>`;
}
