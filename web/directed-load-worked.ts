/** Numerical explanation for line loads beyond the compiled vertical-load checker. */
import { analyse, lineLoadAxis, position, type Model } from './engine.js';
import { loadLabels, loadLabelLatex } from './load-labels.js';
import { math, measureUnits, quantity } from './math.js';
import { sampleSection } from './responses.js';
import { memberLabel } from './model-view.js';
import { formatNumber, formatSectionResult } from './ui.js';

export function directedLoadWorked(model: Model, member: string, t: number, side: 'left' | 'right') {
    const labels = loadLabels(model);
    const rows = model.loads.filter(load => load.kind === 'distributed').map(load => {
        const a = position(model, load.member, 0), b = position(model, load.member, 1);
        const length = Math.hypot(b.x - a.x, b.y - a.y);
        const c = (b.x - a.x) / length, s = (b.y - a.y) / length;
        const axis = lineLoadAxis(load, c, s);
        const components = (intensity: number) => math(quantity(
            '(' + formatNumber((c*axis.x+s*axis.y)*intensity) + ', ' + formatNumber((-s*axis.x+c*axis.y)*intensity) + ')',
            String.raw`\mathrm{kN}/\mathrm{m}`));
        const member = model.members.find(member => member.id === load.member)!;
        const reference = load.direction === 'member-normal' ? 'the member normal'
            : math(String(load.direction ?? 90) + '^\\circ') + ' counterclockwise from global ' + math('+x');
        return '<li>On member ' + memberLabel(model, member) + ', ' + math(loadLabelLatex(labels.get(load.id)!))
            + ' acts along ' + reference + '. Its local axial and transverse intensities are '
            + components(load.fy) + ' at the load start and ' + components(load.qEnd) + ' at the load end.</li>';
    });
    const result = analyse(model);
    const cut = sampleSection(result, member, t, side, model);
    const readout = cut ? [
        math('N=' + quantity(formatSectionResult(cut.N), measureUnits.force)),
        math('V=' + quantity(formatSectionResult(cut.V), measureUnits.force)),
        math('M=' + quantity(formatSectionResult(cut.M), measureUnits.moment)),
    ].join(', ') : 'A numerical section result is unavailable for this drawing and cut.';
    return '<h3>Resolve the distributed loads</h3><p>For member direction cosines '
        + math('(c,s)') + ', resolve the global intensity into local components '
        + math('p=cw_x+sw_y') + ' and ' + math('q=-sw_x+cw_y') + ' per metre of member. Each varies linearly between its end values.</p><ul>'
        + rows.join('') + '</ul><p>Section equilibrium gives ' + math(String.raw`\mathrm dN/\mathrm dx=-p`)
        + ', ' + math(String.raw`\mathrm dV/\mathrm dx=q`) + ' and ' + math(String.raw`\mathrm dM/\mathrm dx=V`)
        + ' between concentrated actions.</p><p>Numerical section response at the selected cut: ' + readout + '</p>';
}
