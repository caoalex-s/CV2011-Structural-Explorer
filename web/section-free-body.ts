import { lineLoadAxis, nodeLabels, type Analysis, type Model, type Sample } from './engine.js';
import { loadLabelLatex, loadLabels } from './load-labels.js';
import { memberLabel } from './model-view.js';
import { math, measureUnits, quantity } from './math.js';
import { sampleSection } from './responses.js';
import { courseColors, forceSymbol, momentSymbol } from './symbols.js';
import { escapeHtml, formatNumber, formatSectionResult } from './ui.js';

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
    const width = 580, height = 224;
    const left = 94, right = 486, y = 102, dimensionY = 184;
    const x = (station: number) => left + (right - left) * station / extent;
    const labels = loadLabels(model);
    const annotations: string[] = [];
    const occupied: { x: number; y: number }[] = [];
    const rows: string[] = [];
    const appliedNames: string[] = [];
    const crowdedLabels: string[] = [];
    const unitForce = (v: number) => Math.abs(v) < 1e-7 ? 0 : v;
    function label(px: number, py: number, latex: string, role: string) {
        annotations.push(`<span class="section-fbd-math" data-fbd-label="${role}" style="left:${100 * px / width}%;top:${100 * py / height}%">${math(latex)}</span>`);
        occupied.push({ x: px, y: py });
    }
    function loadLabel(px: number, py: number, latex: string, role = 'applied') {
        // Give nearby actions separate label lanes while keeping every arrow on
        // its original line of action. The expanded action list gives exact stations.
        for (const lane of [py, 49, 25, 157, 14]) {
            if (occupied.every(other => Math.abs(other.x - px) >= 48 || Math.abs(other.y - lane) >= 23)) {
                label(px, lane, latex, role);
                return;
            }
        }
        crowdedLabels.push(math(latex));
    }
    function actionRow(station: number, X: number, Y: number, C: number, name: string) {
        const position = math('x = ' + quantity(formatNumber(station * length), measureUnits.length));
        const components = math(quantity(`(${formatNumber(X)}, ${formatNumber(Y)})`, measureUnits.force));
        rows.push(`<li>${name} at ${position}, with force ${components} and couple ${math(quantity(formatNumber(C), measureUnits.moment))}.</li>`);
    }
    function externalAction(station: number, fx: number, fy: number, moment: number, name: string, color: string, gap = 0) {
        const X = unitForce(fx), Y = unitForce(fy), C = unitForce(moment);
        actionRow(station, X, Y, C, name);
        return forceSymbol(x(station), y, X, Y, color, '', 42, gap)
            + momentSymbol(x(station), y, C, color, '', 34);
    }
    const opposite = retainRight ? 1 : 0;
    const endValues = sampleSection(analysis, memberId, opposite, retainRight ? 'left' : 'right', model);
    if (!endValues) return '<p>The numerical mesh combines actions near the member end. Its end resultant cannot be separated for this free body.</p>';
    const sign = retainRight ? 1 : -1;
    const cutX = x(t), endX = x(opposite), outward = -sign;
    const node = nodeLabels(model).get(retainRight ? end.id : start.id)!;
    const endFx = unitForce(sign * endValues.N), endFy = unitForce(-sign * endValues.V);
    const endMoment = unitForce(sign * endValues.M);
    const cutFx = unitForce(-sign * cut.N), cutFy = unitForce(sign * cut.V), cutMoment = unitForce(-sign * cut.M);
    label(endX, y - 19, node, 'end');
    label((left + right) / 2, dimensionY - 14, retainRight ? 'L' : 'x', 'dimension');
    label(cutX, dimensionY + 22, '\\text{Cut}', 'cut');
    const endForceSymbol = endFx && endFy ? `R_{${node}}` : `${node}_{${endFx ? 'x' : 'y'}}`;
    if (endFx || endFy) label(endX - outward * 38, endFy < 0 ? y - 39 : y + 49, endForceSymbol, 'end-force');
    if (endMoment) label(endX + outward * 40, y - 42, `M_{${node}}`, 'end-couple');
    if (cutFx) label(cutX + outward * 53, y - 22, 'N(x)', 'normal');
    if (cutFy) label(cutX + outward * 32, y + 48, 'V(x)', 'shear');
    if (cutMoment) label(cutX + outward * 45, y - 30, 'M(x)', 'moment');
    let arrows = externalAction(opposite, endFx, endFy, endMoment, 'Net member-end action', courseColors.reaction);
    const includes = (station: number) => station > 0 && station < 1 &&
        (retainRight || station < t || station === t && side === 'right');
    for (const load of model.loads.filter(load => load.member === memberId)) {
        const label = labels.get(load.id)!;
        let drawing = '';
        if (load.kind === 'distributed') {
            const stop = Math.min(extent, load.end);
            if (stop <= load.t) continue;
            const intensity = (station: number) => load.fy + (load.qEnd - load.fy) * (station - load.t) / (load.end - load.t);
            const axis = lineLoadAxis(load, c, s);
            const axial = c*axis.x + s*axis.y, transverse = -s*axis.x + c*axis.y;
            const maximum = Math.max(Math.abs(intensity(load.t)), Math.abs(intensity(stop)), 1e-12);
            for (let i = 0; i <= 5; i++) {
                const station = load.t + (stop - load.t) * i / 5;
                const q = intensity(station);
                drawing += forceSymbol(x(station), y, axial*q, transverse*q, courseColors.force, '', 43*Math.abs(q)/maximum, 0);
            }
            const station = (value: number) => math('x = ' + quantity(formatNumber(value), measureUnits.length));
            const loadIntensity = (value: number) => math(quantity(formatNumber(value), '\\mathrm{kN/m}'));
            loadLabel(x((load.t + stop) / 2), y - 64, loadLabelLatex(label));
            rows.push(`<li>${math(loadLabelLatex(label))} acts from ${station(load.t*length)} to ${station(stop*length)}, with ${load.direction === undefined ? 'global vertical intensity' : load.direction === 'member-normal' ? 'intensity along local ' + math('+y') : 'intensity along global ' + math(String(load.direction) + '^\\circ')} from ${loadIntensity(intensity(load.t))} to ${loadIntensity(intensity(stop))}.</li>`);
        } else if (includes(load.t)) {
            const X = load.kind === 'force' ? c*load.fx+s*load.fy : 0;
            const Y = load.kind === 'force' ? -s*load.fx+c*load.fy : 0;
            const C = load.kind === 'moment' ? load.mz : 0;
            const latex = loadLabelLatex(label);
            if (unitForce(Math.hypot(X, Y))) {
                loadLabel(x(load.t) - 30 * X / Math.hypot(X, Y), Y > 0 ? y + 59 : y - 61, latex);
            } else if (unitForce(C)) {
                loadLabel(x(load.t) - outward * 36, y + 53, latex);
            }
            drawing = externalAction(load.t, X, Y, C, math(latex), courseColors.force, load.t === t ? 8 : 0);
        } else continue;
        appliedNames.push(label);
        arrows += `<g data-load-id="${escapeHtml(load.id)}">${drawing}</g>`;
    }
    for (const reaction of analysis.reactions) {
        const support = model.supports.find(p => p.member === memberId && reaction.supports.includes(p.id) && includes(p.t));
        if (support) {
            const latex = `R_{${model.supports.indexOf(support) + 1}}`;
            loadLabel(x(support.t), y + 61, latex, 'end-force');
            arrows += externalAction(support.t, c*reaction.fx+s*reaction.fy, -s*reaction.fx+c*reaction.fy,
                reaction.mz, 'Support reaction ' + math(latex), courseColors.reaction);
        }
    }
    actionRow(t, cutFx, cutFy, cutMoment, 'Cut action');
    // Give the zigzag room by leaving a small gap along the action line.
    arrows += `<g data-cut-action="N">${forceSymbol(cutX, y, cutFx, 0, courseColors.force, '', 36, 8, cutFx*outward > 0)}</g>
        <g data-cut-action="V">${forceSymbol(cutX, y, 0, cutFy, courseColors.force, '', 36, 8, cutFy < 0)}</g>
        <g data-cut-action="M">${momentSymbol(cutX, y, cutMoment, courseColors.force, '', 21)}</g>`;
    const station = formatNumber(t*length);
    const body = `Member ${escapeHtml(memberLabel(model, member))}`;
    const caption = `${body} at x = ${station} m (just ${side})`;
    const cutActions = [
        math('N = ' + quantity(formatSectionResult(cut.N), measureUnits.force)),
        math('V = ' + quantity(formatSectionResult(cut.V), measureUnits.force)),
        math('M = ' + quantity(formatSectionResult(cut.M), measureUnits.moment)),
    ].join(' ');
    return `<figure><figcaption>${body} at ${math('x = ' + quantity(station, measureUnits.length))} (just ${side})</figcaption><div class="section-fbd-plot"><svg id="section-fbd" viewBox="0 0 ${width} ${height}" role="img"
        data-member="${escapeHtml(memberId)}" data-parameter="${t}" data-side="${side}" aria-label="${caption}. Retained ${retainRight ? 'end' : 'start'} portion. Applied actions: ${escapeHtml(appliedNames.join(', ') || 'none')}." aria-describedby="fbd-description">
        <title>${caption}. Retained ${retainRight ? 'end' : 'start'} portion in member axes.</title>
        <path class="section-fbd-guide" d="M${left} ${dimensionY}H${right}M${left} ${dimensionY-9}v18M${right} ${dimensionY-9}v18
            M${left-5} ${dimensionY+5}l10-10M${right-5} ${dimensionY+5}l10-10"/>
        <path class="section-fbd-member" d="M${left} ${y}H${right}" stroke="${courseColors.member}"/>
        <path class="section-fbd-face" data-cut-face data-origin-x="${cutX}" data-origin-y="${y}" stroke="${courseColors.member}"
            d="M${cutX} ${y-23}v15l7 4-14 8 7 4v15"/>
        ${arrows}</svg><div class="section-fbd-labels" aria-label="Diagram notation">${annotations.join('')}</div></div>
        ${crowdedLabels.length ? `<p>Additional actions on this portion include ${crowdedLabels.join(', ')}.</p>` : ''}
        <p class="fbd-values">${cutActions}</p>
        <p class="small" id="fbd-description">The zigzag marks the cut on the retained ${retainRight ? 'end' : 'start'} portion. The local coordinate ${math('x')} runs from the member start to its end. The arrows show the actual directions and the values use the section sign convention.</p>
        <details><summary>Forces and couples on the free body</summary><p>Force components are in member axes. Couples in this list are positive counterclockwise. The net action at ${math(node)} includes the forces and couples transferred or applied at that end.</p><ul>${rows.join('')}</ul></details></figure>`;
}
