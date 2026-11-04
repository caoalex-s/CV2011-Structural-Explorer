/** Section readouts, support reactions, stability, and response explanations. */
import { nodeLabels, position } from './engine.js';
import type { Analysis, Model, Sample } from './engine.js';
import { courseColors } from './symbols.js';
import { memberLabel } from './model-view.js';
import { math } from './math.js';
import { element as $, escapeHtml as escape, formatNumber as number } from './ui.js';

interface ResponseOptions {
    model: Model;
    analysis: Analysis;
    currentMember: string;
    sectionT: number;
    layer: string;
    resultsVisible: boolean;
}

/** Interpolate the displayed sample, retaining the right-hand convention at jumps. */
export function sampleSection(analysis: Analysis, currentMember: string, sectionT: number): Sample | undefined {
    const elements = analysis.elements.filter(e => e.member === currentMember);
    // At a point action use the right-hand section, except at the member end.
    const element = elements.find(e => sectionT >= e.t0 - 1e-9 && sectionT < e.t1 - 1e-9) || elements.at(-1);
    if (!element)
        return;
    const u = Math.max(0, Math.min(40, (sectionT - element.t0) / (element.t1 - element.t0) * 40));
    const left = element.samples[Math.floor(u)], right = element.samples[Math.min(40, Math.ceil(u))], fraction = u - Math.floor(u);
    const sample = { ...left };
    for (const key of ['N', 'V', 'M', 'ux', 'uy', 'rotation'] as const)
        sample[key] = left[key] + fraction * (right[key] - left[key]);
    return sample;
}

/** Present the current analysis without recalculating or modifying the model. */
export function renderResponses(options: ResponseOptions): void {
    const { model, analysis, currentMember, sectionT, layer, resultsVisible } = options;
    $<HTMLSelectElement>('section-member').innerHTML = model.members.map(m => `<option value="${escape(m.id)}" ${m.id === currentMember ? 'selected' : ''}>${memberLabel(model, m)}</option>`).join('');
    const member = model.members.find(m => m.id === currentMember);
    const length = member ? Math.hypot(position(model, member.id, 1).x - position(model, member.id, 0).x, position(model, member.id, 1).y - position(model, member.id, 0).y) : 0;
    $('section-distance').textContent = `x = ${number(sectionT * length)} / ${number(length)} m`;
    const sample = sampleSection(analysis, currentMember, sectionT);
    const responseFields = ['N', 'V', 'M', 'rotation', 'displacement'];
    $('section-results').innerHTML = [['Normal force N', sample?.N, 'kN'], ['Shear force V', sample?.V, 'kN'], ['Bending moment M', sample?.M, 'kN m'], ['Physical rotation θ (CCW +)', sample ? sample.rotation * 1000 : undefined, 'mrad'], ['Vertical displacement v (upward +)', sample ? sample.uy * 1000 : undefined, 'mm']].map(([label, value, unit], index) => `<div class="metric ${responseFields[index] === layer ? 'is-current' : ''}"><small>${label}</small><strong>${value === undefined ? '—' : number(Number(value), 4)} <em>${unit}</em></strong></div>`).join('');
    // Classification stays visible; solver diagnostics are available on demand.
    const statusExpanded = $('status').querySelector('details')?.open ?? false;
    const classification = analysis.degree === 0 ? 'Statically determinate' : `Statically indeterminate (${analysis.degree})`;
    $('status').innerHTML = analysis.status === 'stable'
        ? `<details class="system-status" ${statusExpanded ? 'open' : ''}><summary><span class="stability-dot" aria-hidden="true"></span>Stable <span class="status-classification">· ${classification}</span></summary><div class="status-diagnostics">Degree of static indeterminacy: ${analysis.degree}. No free motion in the small-displacement model. Restrained stiffness matrix has full rank.<br>Equilibrium residual: ${analysis.residual!.toExponential(1)}</div></details>`
        : `<span class="status-pill ${analysis.status}">${analysis.status === 'unstable' ? 'Unstable (mechanism)' : analysis.status === 'empty' ? 'Start drawing' : 'Check model'}</span><span class="status-message">${escape(analysis.message)}</span>`;
    $('reactions').innerHTML = analysis.reactions.map((r, i) => {
        const node = model.nodes.find(node => Math.hypot(node.x - r.x, node.y - r.y) < 1e-7);
        const name = node ? `Node ${nodeLabels(model).get(node.id)}` : `Support ${i + 1}`;
        const label = node ? nodeLabels(model).get(node.id)! : 'R';
        const component = (direction: string) => `${label}_{${node ? '' : i + 1}${direction}}`;
        return `<div class="reaction-row"><b>${name} · (${number(r.x)}, ${number(r.y)}) m</b><span>${math(component('x'))}: ${number(r.fx)} · ${math(component('y'))}: ${number(r.fy)} kN</span>${Math.abs(r.mz) > 1e-7 ? `<span>${math(`M_{${node ? label : `R${i+1}`}}`)}: ${number(r.mz)} kN m (CCW +)</span>` : ''}</div>`;
    }).join('');
    $('reactions').hidden = !resultsVisible;
    (document.querySelector('.support-reactions') as HTMLElement).hidden = analysis.status !== 'stable' || (!resultsVisible);
    $('section-results').hidden = !resultsVisible;
    const descriptions: Record<string, [
        string,
        string
    ]> = { M: ['Bending moment', 'For a horizontal member directed rightward, positive M is sagging with tension at the bottom. The Week 4 lecture plots on the tension side; worked tutorials plot on the compression side. Changing the plotting side preserves the signed moment. For an inclined member, use its local axis from the first joint to the second.'], V: ['Shear force', 'Positive V acts downward on the right cut face of the retained left portion. On the opposite cut face its arrow reverses. Between concentrated actions, dM/dx = V and dV/dx = −w for downward-positive distributed intensity w.'], N: ['Normal force', 'Positive normal force N represents tension. Negative values represent compression. The local member axis runs from the first joint to the second.'], displacement: ['Deflected shape and elastic curve', 'The elastic curve gives signed displacement, with vertical v positive upward. Physical slope θ = dv/dx is counterclockwise-positive for rightward x and small rotations. The drawing magnifies displacement; numerical values retain their actual magnitude. The frame solver includes bending and axial deformation.'], none: ['Structural model', 'Click a joint, support, load, or member to inspect it. Snap to a member interior while drawing to create a rigid connection. Crossing members remain separate.'] };
    $('response-title').textContent = descriptions[layer][0];
    $('response-description').textContent = descriptions[layer][1];
    $('legend').innerHTML = `<div class="legend-item"><span class="swatch" style="background:${courseColors.force}"></span>Applied forces and moments</div><div class="legend-item"><span class="swatch" style="background:${courseColors.reaction}"></span>Reactions and displaced shape</div><p class="small">● Rigid continuity · ○ Pin / hinge<br>Spiral: rotational spring<br>Circle between rails: sliding joint<br>◇ Member-specific constraints</p><p class="small">Forces stay on their lines of action. Moment arcs are centred at their application points. A ground pin does not create an internal hinge.</p><p class="small">At a point action the section readout uses the right-hand limit, except at the member end. Values between plotted samples are interpolated.</p>`;
}
