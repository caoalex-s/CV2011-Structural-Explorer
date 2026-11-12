/** Concise course presentation. Only fixed rules and generated numeric tokens
 * enter KaTeX; drawing identifiers and labels enter escaped HTML text. */
import { math, numberLatex } from './math.js';
import { loadLabels, loadLabelText } from './load-labels.js';
import { frameDescriptions, frameStatus } from './frame-display.js';
import { type FrameWorkedSolution, type WorkedStep, validateFrameWorked } from './frame-worked.js';
import { symbols, expression } from './frame-worked-rules.js';
import type { Rational } from './portal-candidate.js';
import { nodeLabels } from './engine.js';
import { memberLabel } from './model-view.js';
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
      <details><summary>Checked mechanism and external work</summary>${frameDescriptions(values).map(text => `<p>${escape(text)}</p>`).join('')}</details>`;
    const labels = loadLabels(model);
    const nodeNames = nodeLabels(model);
    const memberName = (id: string) => memberLabel(model, model.members.find(member => member.id === id)!);
    const pointName = (point: CheckedFramePoint) => point.owner === 'node' ? nodeNames.get(point.id)! :
        `${memberName(point.id)} (t ≈ ${Number(point.parameter.numerator) / Number(point.parameter.denominator)})`;
    const selected = model.members.find(member => member.id === query.member)!;
    const interval = report.interval!;
    const inputRows = model.loads.map(load => `<tr><td>${escape(loadLabelText(labels.get(load.id)!))}</td><td>${escape(memberName(load.member))}</td>
      <td>${load.kind === 'distributed' ? `t = ${load.t} to ${load.end}` : `t = ${load.t}`}</td><td>${load.kind === 'force' ? `Fx = ${load.fx} kN, Fy = ${load.fy} kN` : load.kind === 'moment' ? `Mz = ${load.mz} kN m` : `vertical intensity = ${load.fy} kN/m`}</td></tr>`).join('');
    const supportRows = model.supports.map((support, index) => `<li>Support ${index + 1}: ${escape(support.kind)}, ${escape(memberName(support.member))} at t = ${support.t}${support.kind === 'roller' ? `, normal angle ${support.angle}°` : ''}.</li>`).join('');
    const reactions = values.points.filter(point => point.reaction?.some(value => value.numerator !== '0') ||
        model.supports.some(support => support.member === point.id && support.t === Number(point.parameter.numerator) / Number(point.parameter.denominator)) ||
        model.supports.some(support => { const member = model.members.find(item => item.id === support.member)!;
            return point.owner === 'node' && ((support.t === 0 && member.a === point.id) || (support.t === 1 && member.b === point.id)); }));
    const reactionRows = reactions.map(point => `<tr><td>${escape(pointName(point))}</td>${point.reaction!.map(value => `<td>${math('\\approx ' + rounded(value))}</td>`).join('')}</tr>`).join('');
    const motionRows = values.points.map(point => `<tr><td>${escape(pointName(point))}</td>${point.motion.map(value => `<td>${math('\\approx ' + rounded(value))}</td>`).join('')}</tr>`).join('');
    const operands = Object.entries(interval.values).map(([key, value]) => `${symbols[key]}\\approx ${rounded(value)}`).join(',\\quad ');
    return `<p class="worked-evidence-summary">The current drawing has a unique linear equilibrium solution. Returned displacements, grouped reactions, and selected section values are checked. Method rules and intermediate substitutions explain these results and are not separately Lean-checked.</p>
      <h3>1. Drawing and selected section</h3>
      <p>Member ${escape(memberName(query.member))} runs from ${escape(nodeNames.get(selected.a)!)} to ${escape(nodeNames.get(selected.b)!)}. Evaluate t = ${query.parameter} using the ${query.cutSide} limit along that direction. Local x follows the member and local y is its counterclockwise normal.</p>
      <p>Axial force N is positive in tension. Bending moment M is positive in sagging with dM/dx = V. Global y is upward and positive rotation is counterclockwise.</p>
      <details><summary>Applied loads, supports, and member properties</summary><table><thead><tr><th>Load</th><th>Member</th><th>Position</th><th>Signed action</th></tr></thead><tbody>${inputRows}</tbody></table><ul>${supportRows}</ul>
        <table><thead><tr><th>Member</th><th>Source ID</th><th>EA (kN)</th><th>EI (kN m²)</th></tr></thead><tbody>${model.members.map(member => `<tr><td>${escape(memberName(member.id))}</td><td>${escape(member.id)}</td><td>${member.EA}</td><td>${member.EI}</td></tr>`).join('')}</tbody></table>
        <table><thead><tr><th>Node</th><th>x (m)</th><th>y (m)</th></tr></thead><tbody>${model.nodes.map(node => `<tr><td>${escape(nodeNames.get(node.id)!)}</td><td>${node.x}</td><td>${node.y}</td></tr>`).join('')}</tbody></table></details>
      <h3>2. Equilibrium and compatibility</h3>
      <p>Let the displacement vector ${math('\\mathbf d')} contain global translations and rotations at the joints and load or support cuts. The restraint matrix ${math('C')} imposes zero motion in supported directions. Assemble stiffness ${math('K')} and consistent loads ${math('\\mathbf F')} from the current members and solve for the free coordinates:</p>
      ${math('C\\mathbf d=0,\\qquad K_{\\mathrm{ff}}\\mathbf d_{\\mathrm f}=\\mathbf F_{\\mathrm f}.', true)}
      <p>The accepted positive LDL factorisation establishes uniqueness for this drawing. The checked displacement vector satisfies the restraints and equilibrium.</p>
      <details><summary>Checked joint and cut displacements</summary><table><thead><tr><th>Point</th><th>ux (m)</th><th>uy (m)</th><th>Rotation (rad)</th></tr></thead><tbody>${motionRows}</tbody></table></details>
      <h3>3. Support reactions</h3>
      <p>The residual gives the grouped support force and moment at each restrained point:</p>${math('\\mathbf R=K\\mathbf d-\\mathbf F.', true)}
      <table><thead><tr><th>Point</th><th>Rx (kN)</th><th>Ry (kN)</th><th>Mz (kN m)</th></tr></thead><tbody>${reactionRows}</tbody></table>
      <p>These returned reactions are checked. Coincident restraints share a grouped reaction without assigning a unique force to each individual restraint.</p>
      <h3>4. Section forces and displacements</h3>
      <p>The selected interval on ${escape(memberName(query.member))} extends from t ≈ ${escape(String(Number(interval.from.numerator) / Number(interval.from.denominator)))} to t ≈ ${escape(String(Number(interval.to.numerator) / Number(interval.to.denominator)))}. Coordinate x is measured from its start. Local displacement components are u and v, with start values u₀, v₀, and θ₀.</p>
      <p>Direction cosines c and s transform global motion into local motion. Uniform load components p and q act along the local x and y axes. The start axial force a₁, transverse force a₂, and moment a₃ follow from the element stiffness and consistent load vector:</p>
      ${math('\\mathbf a=k_e\\mathbf d_e-\\mathbf f_e.', true)}
      <details><summary>Current interval and explanatory intermediate values</summary>${math(operands + '.', true)}<p>Values are reconstructed with exact rational arithmetic from the accepted displacement vector. The compiled checker does not separately check these printed intermediate equations.</p></details>
      ${report.steps.filter(step => ['N', 'V', 'M'].includes(step.id)).map(field).join('')}
      <details><summary>Rotation and global displacements</summary><p>Integrating the loaded axial and bending fields retains the uniform-load particular terms. Global displacement follows ${math('u_x=cu-sv,\\;u_y=su+cv')}.</p>${report.steps.filter(step => ['rotation', 'ux', 'uy'].includes(step.id)).map(field).join('')}</details>
      <details><summary>Derivation rules and verification coverage</summary><p>The accepted source geometry, constraints, assembly, equilibrium, positive stability factor, grouped reactions, and selected loaded fields are covered by <code>RationalFrameSoundness.acceptance_actual_frame</code>. Expanded substitutions are explanatory. Changing the drawing or section invalidates this solution.</p><ul>${report.steps.map(step => `<li>${escape(step.id)}: ${escape(step.predicate)}. Rule ${escape(step.rule)} (${escape(step.version)}).</li>`).join('')}</ul><p>Exact source, query, returned values, explanatory records, and checker identities are included in the certificate export.</p></details>`;
}
