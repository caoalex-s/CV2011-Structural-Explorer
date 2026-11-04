/** Human-readable course methods, tied to an exact model/section snapshot. */
import type { Model } from './engine.js';
import { equationHtml, math, methodRules, numberLatex, rationalLatex } from './math.js';
import type { Equation } from './math.js';
import { renderKeyQuantities } from './quantities.js';
import type { KeyQuantities } from './quantities.js';
import { findPublishedExample, loadPublishedLibrary, publishedSolution } from './published-worked.js';
import type { PublishedExample } from './published-worked.js';
import { resolveLoadNotation } from './load-labels.js';
import { pointForceRules } from './point-force-rules.js';
import { pointForceWorked } from './point-force-worked.js';
import { realPointForceApplies } from './real-beam-status.js';
import type { RealBeamReceipt } from './real-beam-status.js';

export interface WorkedResponse {
    title: string;
    section: string;
    length: string;
    assumptions: string;
    conventions: string;
    supports: { a: string; b: string };
    equilibrium: Equation[];
    equilibriumRule: string;
    actions: { symbol?: string; position: string; fx: string; fy: string; couple: string; arm: string; included: boolean }[];
    pieces: { interval: string; intervalLatex?: string; forces: Equation[]; integrations: Equation[]; displacements: Equation[] }[];
    constants: Equation[];
    selected: Equation[];
    momentArea: { title: string; equation: Equation; terms: Equation[] }[];
    thetaLeft: Equation;
    virtual: { reactions: Equation[]; rows: { interval: string; intervalLatex?: string; equations: Equation[] }[]; result: Equation };
    superposition: Equation[];
    quantities: KeyQuantities;
    proof: { status: string; message: string; scope: string; sha256: string; source: string; projectZip: string; groups: Record<string, string[]> };
    sources: string[];
    parameters?: Equation[];
    symbolicScope?: string;
}
interface Context {
    model: Model;
    section: number;
    practice: boolean;
    connected: boolean;
    request: (payload: unknown) => Promise<WorkedResponse>;
    reveal: () => void;
    selectSection: (section: number) => void;
}

const escape = (value: unknown) => String(value).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]!));
let context: Context;
let snapshot = '';
let expanded = false;
let response: WorkedResponse | undefined;
let pending = false;
let timer: ReturnType<typeof setTimeout>;
let method = 'quantities';
let error = '';
let publishedExample: PublishedExample | undefined;
let publishedLoaded = false;
let genericProofStatus = 'loading';
let realBeamReceipt: RealBeamReceipt | undefined;
void fetch('verification.json').then(result => {
    if (!result.ok) throw Error('Proof receipt unavailable');
    return result.json();
}).then(receipt => {
    genericProofStatus = receipt.lean === 'checked' ? 'checked' : 'pending';
    realBeamReceipt = receipt.realBeam;
})
    .catch(() => { genericProofStatus = 'pending'; })
    .finally(() => { if (context && expanded) draw(); });

/** Display the generic theorem separately from any numerical certificate. */
function genericRules(): string {
    const rule = pointForceRules(context.model, context.section);
    if (!rule) return '<p class="small">The single point-force generic rules do not apply to this drawing. Other worked methods may have separate instance certificates.</p>';
    const n = numberLatex;
    const P = rule.label, force = `(${n(rule.P)})`, left = `(${n(rule.leftReaction)})`;
    const shear = rule.after ? `A_y-${P}` : 'A_y';
    const moment = rule.after ? `A_y x-${P}(x-a)` : 'A_y x';
    const elastic = pointForceWorked(context.model, context.section);
    const offlineDerivation = !context.connected && !response && elastic
        ? pointForceDerivation(elastic, realPointForceApplies(context.model, context.section, realBeamReceipt)) : '';
    if (response) return `<p class="small">${genericProofStatus === 'checked' ? 'Lean checked generic equilibrium and section rules apply.' : 'Generic equilibrium and section proof status pending.'} ${realPointForceApplies(context.model, context.section, realBeamReceipt) ? 'Lean also checked generic real-field derivative and branch-continuity rules.' : ''} These rules are distinct from the numerical certificate below. ${rule.maximum ? '' : 'The nonnegative-load maximum rule does not apply.'}</p>`;
    return `<details class="worked-assumptions" open><summary>Parameterized point-force rules and worked derivation</summary>
        <p class="small">${genericProofStatus === 'checked' ? 'Lean checked generic rules' : 'Generic proof status pending'}: reaction equilibrium, section equilibrium, shear jump and moment continuity. These are parameterized rules, not a certificate for this numerical model. ${rule.maximum ? 'The nonnegative-load maximum-moment rule also applies.' : 'The maximum-moment rule requires a nonnegative downward load and does not apply.'}</p>
        <p class="small">${math(`${P}=-F_y=${n(rule.P)}\\,\\mathrm{kN},\\quad L=${n(rule.L)}\\,\\mathrm m,\\quad a=${n(rule.a)}\\,\\mathrm m,\\quad x=${n(rule.x)}\\,\\mathrm m`)}; ${rule.after ? 'x ≥ a (right-hand cut)' : rule.x === rule.a ? 'x = a (left-hand endpoint limit)' : 'x < a'}.</p>
        ${math(`B_y=\\frac{${P}a}{L}=\\frac{${force}(${n(rule.a)})}{${n(rule.L)}}\\approx ${n(rule.rightReaction)},\\quad A_y=\\frac{${P}(L-a)}{L}\\approx ${n(rule.leftReaction)}`, true)}
        ${math(`V=${shear}=${left}${rule.after ? `-${force}` : ''}\\approx ${n(rule.shear)},\\quad M=${moment}=${left}(${n(rule.x)})${rule.after ? `-${force}(${n(rule.x)}-${n(rule.a)})` : ''}\\approx ${n(rule.moment)}`, true)}
        <p class="small">The proof uses cleared-denominator integer statements for rational inputs. Drawing conversion, physical assumptions, and rendering are outside the proof.</p>${offlineDerivation}</details>`;
}

/** Offline course methods for the same bounded family, without an instance certificate. */
export function pointForceDerivation(rule: NonNullable<ReturnType<typeof pointForceWorked>>, realChecked = false): string {
    const n = numberLatex;
    const P = rule.label;
    const slopeBranch = rule.after ? `-${P}(x-a)^2` : '';
    const deflectionBranch = rule.after ? `-${P}(x-a)^3` : '';
    const slopeNumbers = `${n(rule.leftReaction)}(${n(rule.x)})^2${rule.after ? `-(${n(rule.P)})(${n(rule.x)}-${n(rule.a)})^2` : ''}`;
    const displacementNumbers = `${n(rule.leftReaction)}(${n(rule.x)})^3${rule.after ? `-(${n(rule.P)})(${n(rule.x)}-${n(rule.a)})^3` : ''}`;
    return `<h3>Double integration</h3>
        <p class="small">${realChecked ? 'Lean checked the generic real-field derivative and branch-continuity rules for this beam family.' : 'Symbolic elastic derivation; generic real-field proof status is pending.'} No Lean certificate is claimed for the current numerical instance. The beam is prismatic, linearly elastic and has constant positive EI. Positive slope is counterclockwise and positive displacement is upward.</p>
        ${math(`EI=${n(rule.EI)}\\,\\mathrm{kN}\\,\\mathrm m^2,\\quad EI v''=M,\\quad v(0)=v(L)=0`, true)}
        ${math(`\\theta(0)=-\\frac{${P}(L-a)\\left[L^2-(L-a)^2\\right]}{6LEI}=-\\frac{(${n(rule.P)})(${n(rule.L)}-${n(rule.a)})[(${n(rule.L)})^2-(${n(rule.L)}-${n(rule.a)})^2]}{6(${n(rule.L)})(${n(rule.EI)})}\\approx ${n(rule.thetaLeft)}\\,\\mathrm{rad}`, true)}
        ${math(`\\theta(x)=\\theta(0)+\\frac{A_yx^2${slopeBranch}}{2EI}=(${n(rule.thetaLeft)})+\\frac{${slopeNumbers}}{2(${n(rule.EI)})}\\approx ${n(rule.theta)}\\,\\mathrm{rad}`, true)}
        ${math(`v(x)=\\theta(0)x+\\frac{A_yx^3${deflectionBranch}}{6EI}=(${n(rule.thetaLeft)})(${n(rule.x)})+\\frac{${displacementNumbers}}{6(${n(rule.EI)})}\\;\\mathrm m\\approx ${n(rule.displacement * 1000)}\\,\\mathrm{mm}`, true)}
        <p class="small">Compare the end slopes for the greatest slope magnitude. The displacement stationary point satisfies ${math(String.raw`\theta(x_v)=0`)}. ${rule.P === 0 || rule.a === 0 || rule.a === rule.L ? 'Here the elastic response is zero everywhere.' : ''}</p>
        ${math(`\\max|\\theta|=\\max(|\\theta(0)|,|\\theta(L)|)\\approx ${n(rule.maximumSlope * 1000)}\\,\\mathrm{mrad}`, true)}
        ${math(`x_v=${rule.a >= rule.L / 2 ? String.raw`\sqrt{a(2L-a)/3}` : String.raw`L-\sqrt{(L-a)(L+a)/3}`}\\approx ${n(rule.stationaryX)}\\,\\mathrm m,\\quad v(x_v)\\approx ${n(rule.stationaryDisplacement * 1000)}\\,\\mathrm{mm},\\quad \\max|v|\\approx ${n(Math.abs(rule.stationaryDisplacement) * 1000)}\\,\\mathrm{mm}`, true)}
        <h3>Moment-area and virtual work</h3>
        <p class="small">The moment-area theorems give the same displacement using the left support tangent. For virtual work, apply a downward unit force at the selected section; its normalised moment is shown on each side of the section. A positive virtual-work result is downward.</p>
        ${math(String.raw`\theta(x)-\theta(0)=\int_0^x\frac{M(s)}{EI}\,\mathrm ds,\quad v(x)=x\theta(0)+\int_0^x\frac{(x-s)M(s)}{EI}\,\mathrm ds`, true)}
        ${math(String.raw`m(s)=\begin{cases}(L-x)s/L,&s<x,\\x(L-s)/L,&s\ge x,\end{cases}\quad \Delta_{\mathrm{down}}=\int_0^L\frac{M(s)m(s)}{EI}\,\mathrm ds=-v(x)`, true)}
        ${math(`\\Delta_{\\mathrm{down}}\\approx ${n(-rule.displacement * 1000)}\\,\\mathrm{mm}`, true)}
        <p class="small">With one force, superposition has one contribution: ${math(`v^{(${P})}(x)=v(x)`)}. For additional loads or other structures, use the connected worked solution.</p>`;
}

function equations(rows: Equation[]): string {
    return rows.map(equationHtml).join('');
}

function proofLabel(groups: string[]): string {
    if (!response) return '';
    const count = groups.reduce((sum, group) => sum + (response!.proof.groups[group]?.length || 0), 0);
    return `<span class="method-proof ${response.proof.status === 'checked' ? 'checked' : ''}">${response.proof.status === 'checked' ? `Lean checked · ${count} ${count === 1 ? 'statement' : 'statements'}` : 'Symbolic result · Lean not checked'}</span>`;
}

function steps(): string {
    const data = response!;
    if (method === 'quantities') return renderKeyQuantities(data.quantities, proofLabel, data);
    const intervals = (field: 'forces' | 'integrations' | 'displacements') => data.pieces.map((piece, i) => `<details class="worked-interval" ${i === 0 ? 'open' : ''}><summary>Interval ${i + 1}: ${math(piece.intervalLatex || piece.interval)}</summary><p class="small">Current coordinates: ${math(piece.interval)} m.</p>${equations(piece[field])}</details>`).join('');
    const selected = `<h3>At the selected section: ${math(`x_s = ${rationalLatex(data.section)}\\,\\mathrm{m}`)}</h3>${equations(data.selected)}`;
    if (method === 'sections') return `
        ${proofLabel(['equilibrium', 'partition', 'sections', 'conventions', 'diagrams', 'jumps', 'ends', 'readout'])}
        <h3>1. Find the support reactions</h3>
        <p>Replace the supports by their reactions. Keep each force at its application point and each couple at its stated sign. Let ${math(`a=${rationalLatex(data.supports.a)}\\,\\mathrm{m}`)} and ${math(`b=${rationalLatex(data.supports.b)}\\,\\mathrm{m}`)} denote the left and right support coordinates.</p>
        <p>Reaction symbols follow the labelled points on the drawing. For an interior support without a node label, ${math('R_{1y}')} or ${math('R_{2y}')} identifies its vertical component. Here ${math(String.raw`F_{\mathrm{tot}}`)} is the signed sum of the applied vertical forces and ${math('T')} is their total external moment, including couples, about ${math('x=0')}.</p>
        <div class="worked-rule">${math(data.equilibriumRule, true)}</div>${equations(data.equilibrium)}
        <h3>2. Cut the beam and balance the left free body</h3>
        <p>For each interval, retain the left portion and show the positive cut actions: normal force ${math('N')} rightward, shear force ${math('V')} downward, and bending moment ${math('M')} counterclockwise. The point-force components ${math('F_{x,i},F_{y,i}')} remain rightward/upward-positive, and the applied couple ${math('C_i')} is counterclockwise-positive. Following Tutorial 5, distributed load intensity ${math('w')} is positive downward. Integrate only the loaded part of this free body and use each force's actual lever arm.</p>
        <div class="worked-rule">${math(methodRules.sections, true)}</div>
        <details><summary>Point actions on the selected free body, including reactions</summary><div class="worked-table"><table class="data-table"><thead><tr><th>Action</th><th>xᵢ (m)</th><th>Fₓ (kN)</th><th>Fᵧ (kN)</th><th>C (kN m)</th><th>Arm (m)</th><th>Included</th></tr></thead><tbody>${data.actions.map(a => `<tr><td>${a.symbol ? math(a.symbol) : ''}</td><td>${escape(a.position)}</td><td>${escape(a.fx)}</td><td>${escape(a.fy)}</td><td>${escape(a.couple)}</td><td>${escape(a.arm)}</td><td>${a.included ? 'Yes' : 'No'}</td></tr>`).join('')}</tbody></table></div></details>
        <h3>3. Build the diagrams interval by interval</h3>
        <p>The following expressions determine the normal-force, shear-force, and bending-moment diagrams. Between point actions, ${math("V'=-w")} and ${math("M'=V")}. At a point force, ${math(String.raw`\Delta V=F_y`)} and ${math(String.raw`\Delta N=-F_x`)}. A counterclockwise couple gives ${math(String.raw`\Delta M=-C`)}. The superscripts ${math('-')} and ${math('+')} mean immediately before and after a section in increasing ${math('x')}. At the right endpoint, exclude actions at the cut when taking the left-hand limit. Insert ${math('x')} in metres in the numerical polynomials.</p>${intervals('forces')}${selected}`;
    if (method === 'integration') return `
        ${proofLabel(['integration', 'conditions', 'continuity', 'readout'])}
        <h3>1. Integrate the moment equation twice</h3><p>The moment equation ${math("EI v''=M")} relates bending moment to curvature through the flexural rigidity ${math('EI')}. For the rightward coordinate ${math('x')}, displacement ${math('v')} is positive upward and physical slope ${math(String.raw`\theta=v'`)} is positive counterclockwise. As in Tutorial 8, each interval introduces two integration constants in ${math(String.raw`EI\theta`)} and ${math('EI v')}. Number them ${math('C_1,C_2')} on the first interval and ${math('C_3,C_4')} on the second, continuing sequentially on later intervals.</p>
        <div class="worked-rule">${math(methodRules.integration, true)}</div>${intervals('integrations')}
        <h3>2. Apply boundary and continuity conditions</h3><p>The pin and roller impose zero vertical displacement at their positions. At each continuous section, both displacement ${math('v')} and physical slope ${math(String.raw`\theta`)} are continuous. These conditions determine the integration constants below. An internal hinge permits a slope discontinuity and is outside this worked beam derivation.</p>
        <div class="worked-rule">${math(methodRules.conditions, true)}</div>${equations(data.constants)}
        <h3>3. Obtain the elastic curve and slope</h3><p>The elastic curve ${math('v(x)')} gives the signed vertical displacement. Its slope ${math(String.raw`\theta(x)`)} gives the physical tangent rotation. The curve's drawing scale is separate from the bending-moment diagram.</p>${intervals('displacements')}${selected}`;
    if (method === 'area') return `
        ${proofLabel(['moment_area'])}
        <h3>1. Apply the moment-area theorems</h3><p>The first theorem gives the change of physical slope between tangent origin ${math('P')} and target ${math('Q')}. The second gives the vertical tangent deviation ${math('t_{Q/P}')} from the tangent at ${math('P')}. Following Tutorial 10, measure each first-moment lever arm from the target ${math('Q')}. Use signed areas of ${math('M/(EI)')}, with positive sagging moment, regardless of which side is selected for plotting.</p>
        <div class="worked-rule">${math(methodRules.area, true)}</div>
        <h3>2. Determine the tangent at the left support</h3><p>Both supports have zero vertical displacement. Applying the second theorem between them gives ${math(String.raw`\theta(a)=-\frac{t_{b/a}}{b-a}`)}. Use this tangent when evaluating displacement at the selected section. Integrals to a point on the left overhang have reversed limits.</p>${equations([data.thetaLeft])}
        <h3>3. Add the interval contributions</h3>${data.momentArea.map(row => `<details class="worked-interval" open><summary>${escape(row.title)}</summary>${equations(row.terms)}${equations([row.equation])}</details>`).join('')}${selected}`;
    if (method === 'virtual') return `
        ${proofLabel(['virtual_work'])}
        <h3>1. Define the virtual system and displacement direction</h3><p>Following Tutorial 12, choose downward-positive displacement ${math(String.raw`\Delta_{s\mathrm v}`)}. Remove the real loads and apply a downward virtual force ${math(String.raw`\bar P=1\,\mathrm{kN}`)} at ${math(`x_s=${rationalLatex(data.section)}\\,\\mathrm{m}`)}. Keep the supports, coordinate origin, and bending-moment sign convention unchanged.</p>${equations(data.virtual.reactions)}
        <h3>2. Normalise the virtual moment and apply virtual work</h3><p>The actual virtual bending moment is ${math(String.raw`\bar M`)} in ${math(String.raw`\mathrm{kN}\,\mathrm m`)}. Divide it by the virtual force to obtain the normalised moment ${math(String.raw`m=\bar M/\bar P`)} in metres. The unit-load expression then gives displacement directly, with no factor ${math('1/2')}.</p><div class="worked-rule">${math(methodRules.virtual, true)}</div><p>Split the integral wherever the real or normalised virtual moment changes. Each contribution below has units of metres. The final displacement is converted to millimetres.</p>
        ${data.virtual.rows.map(row => `<details class="worked-interval" open><summary>${math(row.intervalLatex || row.interval)}</summary><p class="small">Current coordinates: ${math(row.interval)} m.</p>${equations(row.equations)}</details>`).join('')}
        <h3>3. Interpret the displacement direction</h3>${equations([data.virtual.result])}<p>A positive result means downward movement in the direction of the virtual force. A negative result means upward movement. The Lean certificate checks ${math(String.raw`\Delta_{s\mathrm v}=-v(x_s)`)} against the upward-positive elastic curve from double integration.</p>`;
    return `${proofLabel(['superposition'])}<h3>1. Keep one real load at a time</h3><p>For this linear beam, each load acts on the same structure with the same supports and stiffness. Calculate the displacement caused by each load separately. Add their signed contributions at the selected position.</p>${equations(data.superposition)}<h3>2. Add the contributions</h3>${equations([data.selected[data.selected.length-1]])}<p>The contribution calculations use the exact symbolic beam reference. The Lean statement for this view checks their sum against the displacement polynomial. Individual contribution derivations are not included in that statement.</p>`;
}

function draw(): void {
    const panel = document.getElementById('worked-panel')!;
    panel.innerHTML = `<div class="worked-heading"><h2>Worked solution</h2><button id="toggle-worked" aria-expanded="${expanded}">${expanded ? 'Collapse' : context.practice ? 'Reveal solution' : 'Show solution'}</button></div>`;
    document.getElementById('toggle-worked')!.onclick = () => {
        expanded = !expanded;
        if (expanded && context.practice) context.reveal();
        draw();
        if (expanded && !response) schedule();
    };
    if (!expanded) return;
    panel.insertAdjacentHTML('beforeend', genericRules());
    if (!context.connected) {
        panel.insertAdjacentHTML('beforeend', '<details class="small"><summary>Using published and edited models</summary><p>Published examples include their derivations and Lean certificates. A single point-force beam also has a symbolic offline derivation. Other edited beams require the <a href="http://localhost:8765/#sandbox" target="_blank" rel="noopener">local workspace</a>. Transfer a drawing with <strong>Save model</strong> here and <strong>Open model</strong> there.</p></details>');
        if (publishedExample) {
            panel.insertAdjacentHTML('beforeend', `<div class="published-sections"><p class="small">${escape(publishedExample.name)}<br>Choose a checked section:</p><div class="dialog-buttons">${publishedExample.solutions.map(solution => `<button data-published-section="${solution.section}" aria-pressed="${solution.section === context.section}">${math(`x_s=${solution.section === 0.5 ? 'L/2' : solution.section === 0.25 ? 'L/4' : '3L/4'}`)}</button>`).join('')}</div></div>`);
            panel.querySelectorAll<HTMLButtonElement>('[data-published-section]').forEach(button => button.onclick = () => context.selectSection(Number(button.dataset.publishedSection)));
        }
        if (publishedLoaded && !response && !error) {
            panel.insertAdjacentHTML('beforeend', `<p role="status">${publishedExample ? 'No published certificate covers the current section. Choose one of the checked sections above or use the local verifier.' : pointForceWorked(context.model, context.section) ? 'The symbolic worked derivation above follows the current drawing. No numerical instance certificate is available offline.' : 'This drawing has no published worked solution. Use a published example or the local verifier for full course-method derivations.'}</p>`);
            return;
        }
    }
    if (!response) {
        panel.insertAdjacentHTML('beforeend', `<p role="status">${escape(error || (context.connected ? 'Deriving the current model and checking its certificate…' : 'Loading the published worked solutions…'))}</p>`);
        if (error) {
            panel.insertAdjacentHTML('beforeend', '<button id="retry-worked">Try again</button>');
            document.getElementById('retry-worked')!.onclick = () => { error = ''; schedule(); draw(); };
        }
        return;
    }
    panel.insertAdjacentHTML('beforeend', `<p class="small" role="status">${response.proof.status === 'checked' ? 'Lean checked for the current numerical model.' : 'Symbolic result. Lean has not checked this numerical model.'}</p>
        ${response.parameters ? `<details class="worked-assumptions"><summary>Input symbols and values</summary>${equations(response.parameters)}</details>` : ''}
        <article class="worked-steps compact-solution">${renderKeyQuantities(response.quantities, proofLabel, response)}</article>
        <details class="full-derivations" ${method !== 'quantities' ? 'open' : ''}><summary>Full course-method derivations</summary>
        <div class="method-tabs" role="group" aria-label="Solution method">${[['sections', 'Method of sections'], ['integration', 'Double integration'], ['area', 'Moment-area theorems'], ['virtual', 'Principle of virtual work'], ['superposition', 'Method of superposition']].map(([id, label]) => `<button data-method="${id}" class="${id === method ? 'active' : ''}" aria-pressed="${id === method}">${label}</button>`).join('')}</div><article class="worked-steps">${method === 'quantities' ? '<p class="small">Choose a method above for its complete interval calculations.</p>' : steps()}</article></details>`);
    // Keep the full course methods and exact certificate accessible without
    // placing their explanatory detail ahead of the short calculation.
    panel.insertAdjacentHTML('beforeend', `<details class="worked-assumptions"><summary>Model, signs, and verification scope</summary><p>${escape(response.proof.message)}</p><p>${escape(response.assumptions)}</p><p>${escape(response.conventions)}</p><p>${escape(response.symbolicScope || '')}</p><p>${escape(response.proof.scope)}</p><p class="small">Course references: ${response.sources.map(escape).join(' · ')}</p><button id="download-proof">Download Lean source</button> <button id="download-proof-project">Download VS Code proof project</button></details>`);
    panel.querySelectorAll<HTMLButtonElement>('[data-method]').forEach(button => button.onclick = () => { method = button.dataset.method!; draw(); });
    document.getElementById('download-proof')!.onclick = () => {
        download(new Blob([response!.proof.source], { type: 'text/plain' }), 'lean');
    };
    document.getElementById('download-proof-project')!.onclick = () => {
        const bytes = Uint8Array.from(atob(response!.proof.projectZip), character => character.charCodeAt(0));
        download(new Blob([bytes], { type: 'application/zip' }), 'zip');
    };
}

function download(blob: Blob, extension: string): void {
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = `WorkedBeam-${response!.proof.sha256.slice(0, 12)}.${extension}`;
    link.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
}

/** The caller records the reveal event before opening this shared view. */
export function showWorkedSolution(preferredMethod: 'sections' | 'integration'): void {
    expanded = true;
    method = preferredMethod;
    draw();
    if (!response) schedule();
    document.getElementById('worked-panel')!.scrollIntoView({ behavior: 'smooth', block: 'start' });
}

function schedule(): void {
    clearTimeout(timer);
    if (expanded && !pending) timer = setTimeout(() => { void fetchSolution(); }, 650);
}

async function fetchSolution(): Promise<void> {
    if (pending || !expanded) return;
    const key = snapshot;
    const payload = { model: structuredClone(context.model), section: context.section };
    pending = true;
    error = '';
    try {
        if (context.connected) {
            const result = await context.request(payload);
            if (key === snapshot) response = resolveLoadNotation(result, payload.model);
        } else {
            const library = await loadPublishedLibrary();
            if (key === snapshot) {
                publishedExample = findPublishedExample(payload.model, library);
                const published = publishedExample ? publishedSolution(publishedExample, payload.section) : undefined;
                response = published ? resolveLoadNotation(published, payload.model) : undefined;
                publishedLoaded = true;
            }
        }
    } catch (failure) {
        if (key === snapshot) error = failure instanceof Error ? failure.message : 'The derivation could not be obtained.';
    } finally {
        pending = false;
        draw();
        if (key !== snapshot) schedule();
    }
}

export function renderWorked(next: Context): void {
    const key = JSON.stringify([next.model, next.section, next.connected]);
    const enteringPractice = next.practice && context && !context.practice;
    const modeChanged = context && next.practice !== context.practice;
    context = next;
    if (key !== snapshot || enteringPractice) {
        snapshot = key;
        response = undefined;
        publishedExample = undefined;
        publishedLoaded = false;
        error = '';
        // New practice questions require an explicit reveal. Exploration
        // refreshes automatically after geometry, load, or section edits.
        if (next.practice) expanded = false;
        draw();
        schedule();
    } else if (modeChanged || !document.getElementById('toggle-worked')) draw();
}
