/** Concise course presentation. Only fixed rules and generated numeric tokens
 * enter KaTeX; drawing identifiers and labels enter escaped HTML text. */
import { math, measureUnits, numberLatex, quantity } from './math.js';
import { loadLabels, loadLabelLatex } from './load-labels.js';
import { frameDescriptions, frameStatus } from './frame-display.js';
import { type FrameWorkedSolution, type WorkedStep, validateFrameWorked } from './frame-worked.js';
import { symbols, expression } from './frame-worked-rules.js';
import type { Rational } from './portal-candidate.js';
import { nodeLabels } from './engine.js';
import { memberLabel, reactionSymbols } from './model-view.js';
import type { CheckedFramePoint } from './frame-result.js';

const escape = (text: string) => text.replace(/[&<>"']/g, character =>
    ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[character]!));
const rounded = (value: Rational) => numberLatex(Number(value.numerator) / Number(value.denominator));
const labels: Record<string, string> = { N: 'N', V: 'V', M: 'M', rotation: '\\theta', ux: 'u_x', uy: 'u_y' };
const units: Record<string, string> = { kN: '\\mathrm{kN}', 'kN m': '\\mathrm{kN}\\,\\mathrm{m}', m: '\\mathrm{m}', rad: '\\mathrm{rad}' };
function field(step: WorkedStep): string {
    const result = step.result!;
    const symbolic = step.symbolicExpression;
    const substituted = expression(step.id, key => `\\left(${rounded(step.inputs[key])}\\right)`);
    const exactSubstitution = step.exactSubstitution;
    return `<div class="worked-equation" data-worked-step="${step.id}" data-evidence="explanatory-rule">
      ${math(`${labels[step.id]}=${symbolic}.`, true)}
      <p>Rounded substitution (explanatory):</p>${math(`${labels[step.id]}\\approx ${substituted}.`, true)}
        <details><summary>Exact rational substitution</summary>${math(`${labels[step.id]}=${exactSubstitution}.`, true)}</details>
      <div data-evidence="verified-result">${math(`${labels[step.id]}\\approx ${rounded(result.value)}\\;${units[result.unit]}.`, true)}<small>Checked result · displayed value rounded</small></div>
    </div>`;
}

export function renderFrameWorked(report: FrameWorkedSolution): string {
    validateFrameWorked(report);
    const { model, values, query } = report;
    if (values.kind === 'mechanism') return `<h3>No unique equilibrium solution</h3><p>${escape(frameStatus(values))}</p>
      <details><summary>Checked mechanism and external work</summary>${frameDescriptions(values, model).map(text => `<p>${escape(text)}</p>`).join('')}</details>`;
    const labels = loadLabels(model);
    const nodeNames = nodeLabels(model);
    const memberName = (id: string) => memberLabel(model, model.members.find(member => member.id === id)!);
    const pointName = (point: CheckedFramePoint) => point.owner === 'node' ? nodeNames.get(point.id)! :
        `${memberName(point.id)} (t ≈ ${Number(point.parameter.numerator) / Number(point.parameter.denominator)})`;
    const selected = model.members.find(member => member.id === query.member)!;
    const interval = report.interval!;
    const scalar = (value: number) => numberLatex(value, 17);
    const action = (name: string, value: number, unit: string) => math(name + '=' + quantity(scalar(value), unit));
    const inputRows = model.loads.map(load => {
        const position = load.kind === 'distributed'
            ? math(String.raw`${scalar(load.t)}\le t\le ${scalar(load.end)}`)
            : math('t=' + scalar(load.t));
        const intensity = (start: number, end: number) => `${math(quantity(scalar(start), '\\mathrm{kN/m}'))} to ${math(quantity(scalar(end), '\\mathrm{kN/m}'))}`;
        const signedAction = load.kind === 'force'
            ? `${action('F_x', load.fx, measureUnits.force)}, ${action('F_y', load.fy, measureUnits.force)}`
            : load.kind === 'moment' ? action('M_z', load.mz, measureUnits.moment)
                : `Upward-positive intensity ${intensity(load.fy, load.qEnd)}. Drawing ${math('w')} runs from ${intensity(-load.fy, -load.qEnd)} (downward positive).`;
        return `<tr><td>${math(loadLabelLatex(labels.get(load.id)!))}</td><td>${escape(memberName(load.member))}</td><td>${position}</td><td>${signedAction}</td></tr>`;
    }).join('');
    const supportRows = model.supports.map((support, index) => `<li>Support ${index + 1}: ${escape(support.kind)}, ${escape(memberName(support.member))} at ${math('t=' + scalar(support.t))}${support.kind === 'roller' ? ', normal angle ' + math(scalar(support.angle) + '^\\circ') : ''}.</li>`).join('');
    const reactions = values.points.filter(point => point.reaction?.some(value => value.numerator !== '0') ||
        model.supports.some(support => support.member === point.id && support.t === Number(point.parameter.numerator) / Number(point.parameter.denominator)) ||
        model.supports.some(support => { const member = model.members.find(item => item.id === support.member)!;
            return point.owner === 'node' && ((support.t === 0 && member.a === point.id) || (support.t === 1 && member.b === point.id)); }));
    const reactionRows = reactions.map(point => {
        const components = reactionSymbols(point.owner === 'node' ? nodeNames.get(point.id) : undefined);
        const cells = point.reaction!.map((value, index) => `<td>${math(components[index] + ' \\approx ' + rounded(value))}</td>`);
        return `<tr><th scope="row">${escape(pointName(point))}</th>${cells.join('')}</tr>`;
    }).join('');
    const motionRows = values.points.map(point => `<tr><td>${escape(pointName(point))}</td>${point.motion.map(value => `<td>${math('\\approx ' + rounded(value))}</td>`).join('')}</tr>`).join('');
    const operands = Object.entries(interval.values).map(([key, value]) => `${symbols[key]}\\approx ${rounded(value)}`).join(',\\quad ');
    return `<p class="worked-evidence-summary">The current drawing has a unique linear equilibrium solution. Returned displacements, grouped reactions, and selected section values are checked. Method rules and intermediate substitutions explain these results and are not separately Lean-checked.</p>
      <h3>1. Drawing and selected section</h3>
      <p>Member ${escape(memberName(query.member))} runs from ${escape(nodeNames.get(selected.a)!)} to ${escape(nodeNames.get(selected.b)!)}. Evaluate ${math('t = ' + numberLatex(query.parameter, 17))} using the ${query.cutSide} limit along that direction. Local ${math('x')} follows the member and local ${math('y')} is its counterclockwise normal.</p>
      <p>Axial force ${math('N')} is positive in tension. Bending moment ${math('M')} is positive in sagging with ${math(String.raw`\mathrm{d}M/\mathrm{d}x = V`)}. Global ${math('y')} is upward and positive rotation is counterclockwise.</p>
      <details><summary>Applied loads, supports, and member properties</summary><table><thead><tr><th>Load</th><th>Member</th><th>Position</th><th>Signed action</th></tr></thead><tbody>${inputRows}</tbody></table><ul>${supportRows}</ul>
        <table><thead><tr><th>Member</th><th>Source ID</th><th>${math('EA')} (kN)</th><th>${math('EI')} (${math('\\mathrm{kN}\\,\\mathrm{m}^2')})</th></tr></thead><tbody>${model.members.map(member => `<tr><td>${escape(memberName(member.id))}</td><td>${escape(member.id)}</td><td>${member.EA}</td><td>${member.EI}</td></tr>`).join('')}</tbody></table>
        <table><thead><tr><th>Node</th><th>${math('x')} (m)</th><th>${math('y')} (m)</th></tr></thead><tbody>${model.nodes.map(node => `<tr><td>${escape(nodeNames.get(node.id)!)}</td><td>${node.x}</td><td>${node.y}</td></tr>`).join('')}</tbody></table></details>
      <h3>2. Equilibrium and compatibility</h3>
      <p>Let the displacement vector ${math('\\mathbf d')} contain global translations and rotations at the joints and load or support cuts. The restraint matrix ${math('C')} imposes zero motion in supported directions. Assemble stiffness ${math('K')} and consistent loads ${math('\\mathbf F')} from the current members and solve for the free coordinates:</p>
      ${math('C\\mathbf d=0,\\qquad K_{\\mathrm{ff}}\\mathbf d_{\\mathrm f}=\\mathbf F_{\\mathrm f}.', true)}
      <p>The accepted positive LDL factorisation establishes uniqueness for this drawing. The checked displacement vector satisfies the restraints and equilibrium.</p>
      <details><summary>Checked joint and cut displacements</summary><table><thead><tr><th>Point</th><th>${math('u_x')} (m)</th><th>${math('u_y')} (m)</th><th>Rotation ${math('\\theta')} (rad)</th></tr></thead><tbody>${motionRows}</tbody></table></details>
      <h3>3. Support reactions</h3>
      <p>The residual gives the grouped support force and moment at each restrained point:</p>${math('\\mathbf R=K\\mathbf d-\\mathbf F.', true)}
      <table><thead><tr><th>Point</th><th>Horizontal force (kN)</th><th>Vertical force (kN)</th><th>Moment (kN m)</th></tr></thead><tbody>${reactionRows}</tbody></table>
      <p>These returned reactions are checked. Positive vertical reactions act upward and positive reaction moments act counterclockwise. Canvas reaction labels show magnitudes, with direction indicated by the arrows. Coincident restraints share a grouped reaction without assigning a unique force to each individual restraint.</p>
      <h3>4. Section forces and displacements</h3>
      <p>The selected interval on ${escape(memberName(query.member))} extends from ${math('t \\approx ' + rounded(interval.from))} to ${math('t \\approx ' + rounded(interval.to))}. Coordinate ${math('x')} is measured from its start. Local displacement components are ${math('u')} and ${math('v')}, with start values ${math('u_0')}, ${math('v_0')}, and ${math('\\theta_0')}.</p>
      <p>Direction cosines ${math('c')} and ${math('s')} transform global motion into local motion. The local axial and transverse load intensities are ${math('p(x)=p_0+k_p x')} and ${math('q(x)=q_0+k_q x')}. Their start values and slopes include every distributed load acting on this interval. The start axial force ${math('a_1')}, transverse force ${math('a_2')}, and moment ${math('a_3')} follow from the element stiffness and consistent load vector:</p>
      ${math('\\mathbf a=k_e\\mathbf d_e-\\mathbf f_e.', true)}
      <details><summary>Current interval and explanatory intermediate values</summary>${math(operands + '.', true)}<p>Values are reconstructed with exact rational arithmetic from the accepted displacement vector. The compiled checker does not separately check these printed intermediate equations.</p></details>
      ${report.steps.filter(step => ['N', 'V', 'M'].includes(step.id)).map(field).join('')}
      <details><summary>Rotation and global displacements</summary><p>Integrating the loaded axial and bending fields retains the affine-load particular terms. Global displacement follows ${math('u_x=cu-sv,\\;u_y=su+cv')}.</p>${report.steps.filter(step => ['rotation', 'ux', 'uy'].includes(step.id)).map(field).join('')}</details>
      <details><summary>Derivation rules and verification coverage</summary><p>The accepted source geometry, constraints, assembly, equilibrium, positive stability factor, grouped reactions, and selected loaded fields are covered by <code>RationalFrameSoundness.acceptance_actual_frame</code>. Expanded substitutions are explanatory. Changing the drawing or section invalidates this solution.</p><ul>${report.steps.map(step => `<li>${escape(step.id)}: ${escape(step.predicate)}. Rule ${escape(step.rule)} (${escape(step.version)}).</li>`).join('')}</ul><p>Exact source, query, returned values, explanatory records, and checker identities are included in the certificate export.</p></details>`;
}
