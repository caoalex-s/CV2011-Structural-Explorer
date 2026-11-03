/** Human-readable course methods, tied to an exact model/section snapshot. */
import type { Model } from './engine.js';
import { equationHtml, math, methodRules, rationalLatex } from './math.js';
import type { Equation } from './math.js';

interface WorkedResponse {
    title: string;
    section: string;
    length: string;
    assumptions: string;
    conventions: string;
    supports: { a: string; b: string };
    equilibrium: Equation[];
    equilibriumRule: string;
    actions: { position: string; fx: string; fy: string; couple: string; arm: string; included: boolean }[];
    pieces: { interval: string; forces: Equation[]; integrations: Equation[]; displacements: Equation[] }[];
    constants: Equation[];
    selected: Equation[];
    momentArea: { title: string; equation: Equation; terms: Equation[] }[];
    thetaLeft: Equation;
    virtual: { reactions: Equation[]; rows: { interval: string; equations: Equation[] }[]; result: Equation };
    superposition: Equation[];
    proof: { status: string; message: string; scope: string; sha256: string; source: string; projectZip: string; groups: Record<string, string[]> };
    sources: string[];
}
interface Context {
    model: Model;
    section: number;
    practice: boolean;
    connected: boolean;
    request: (payload: unknown) => Promise<WorkedResponse>;
    reveal: () => void;
}

const escape = (value: unknown) => String(value).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]!));
let context: Context;
let snapshot = '';
let expanded = false;
let response: WorkedResponse | undefined;
let pending = false;
let timer: ReturnType<typeof setTimeout>;
let method = 'sections';
let error = '';

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
    const intervals = (field: 'forces' | 'integrations' | 'displacements') => data.pieces.map((piece, i) => `<details class="worked-interval" ${i === 0 ? 'open' : ''}><summary>Interval ${i + 1}: ${math(piece.interval)} m</summary>${equations(piece[field])}</details>`).join('');
    const selected = `<h3>At the selected section: ${math(`x_s = ${rationalLatex(data.section)}\\,\\mathrm{m}`)}</h3>${equations(data.selected)}`;
    if (method === 'sections') return `
        ${proofLabel(['equilibrium', 'partition', 'sections', 'conventions', 'diagrams', 'jumps', 'ends', 'readout'])}
        <h3>1. Find the support reactions</h3>
        <p>Replace the supports by their reactions. Keep each force at its application point and each couple at its stated sign. Let ${math(`a=${rationalLatex(data.supports.a)}\\,\\mathrm{m}`)} and ${math(`b=${rationalLatex(data.supports.b)}\\,\\mathrm{m}`)} denote the left and right support coordinates.</p>
        <p>Reaction symbols follow the labelled points on the drawing. For an interior support without a node label, ${math('R_{1y}')} or ${math('R_{2y}')} identifies its vertical component. Here ${math('F')} is the signed sum of the applied vertical forces and ${math('T')} is their total external moment, including couples, about ${math('x=0')}.</p>
        <div class="worked-rule">${math(data.equilibriumRule, true)}</div>${equations(data.equilibrium)}
        <h3>2. Cut the beam and balance the left free body</h3>
        <p>For each interval, retain the left portion and show the positive cut actions: normal force ${math('N')} rightward, shear force ${math('V')} downward, and bending moment ${math('M')} counterclockwise. The point-force components ${math('F_{x,i},F_{y,i}')} remain rightward/upward-positive, and the applied couple ${math('C_i')} is counterclockwise-positive. Following Tutorial 5, distributed load intensity ${math('w')} is positive downward. Integrate only the loaded part of this free body and use each force's actual lever arm.</p>
        <div class="worked-rule">${math(methodRules.sections, true)}</div>
        <details><summary>Point actions on the selected free body, including reactions</summary><div class="worked-table"><table class="data-table"><thead><tr><th>xᵢ (m)</th><th>Fₓ (kN)</th><th>Fᵧ (kN)</th><th>C (kN m)</th><th>Arm (m)</th><th>Included</th></tr></thead><tbody>${data.actions.map(a => `<tr><td>${escape(a.position)}</td><td>${escape(a.fx)}</td><td>${escape(a.fy)}</td><td>${escape(a.couple)}</td><td>${escape(a.arm)}</td><td>${a.included ? 'Yes' : 'No'}</td></tr>`).join('')}</tbody></table></div></details>
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
        ${data.virtual.rows.map(row => `<details class="worked-interval" open><summary>${math(row.interval)} m</summary>${equations(row.equations)}</details>`).join('')}
        <h3>3. Interpret the displacement direction</h3>${equations([data.virtual.result])}<p>A positive result means downward movement in the direction of the virtual force. A negative result means upward movement. The Lean certificate checks ${math(String.raw`\Delta_{s\mathrm v}=-v(x_s)`)} against the upward-positive elastic curve from double integration.</p>`;
    return `${proofLabel(['superposition'])}<h3>1. Keep one real load at a time</h3><p>For this linear beam, each load acts on the same structure with the same supports and stiffness. Calculate the displacement caused by each load separately. Add their signed contributions at the selected position.</p>${equations(data.superposition)}<h3>2. Add the contributions</h3>${equations([data.selected[data.selected.length-1]])}<p>The contribution calculations use the exact symbolic beam reference. The Lean statement for this view checks their sum against the displacement polynomial. Individual contribution derivations are not included in that statement.</p>`;
}

function draw(): void {
    const panel = document.getElementById('worked-panel')!;
    panel.innerHTML = `<div class="worked-heading"><div><div class="panel-label">COURSE METHODS</div><h2>How is this response obtained?</h2></div><button id="toggle-worked">${expanded ? 'Hide worked solution' : context.practice ? 'Reveal full worked solution' : 'Show worked solution'}</button></div>`;
    document.getElementById('toggle-worked')!.onclick = () => {
        expanded = !expanded;
        if (expanded && context.practice) context.reveal();
        draw();
        if (expanded && !response) schedule();
    };
    if (!expanded) return;
    panel.insertAdjacentHTML('beforeend', '<p class="small">Supported: one horizontal beam, one pin, and one vertical roller, including overhangs and up to 12 mixed loads. Frames and joint springs remain available in the numerical sandbox.</p>');
    if (!context.connected) {
        panel.insertAdjacentHTML('beforeend', '<p>Open the local pilot or connect the course verifier to derive your current model. The GitHub interface does not run Lean in the browser.</p>');
        return;
    }
    if (!response) {
        panel.insertAdjacentHTML('beforeend', `<p role="status">${escape(error || 'Deriving the current model and checking its certificate…')}</p>`);
        if (error) {
            panel.insertAdjacentHTML('beforeend', '<button id="retry-worked">Try again</button>');
            document.getElementById('retry-worked')!.onclick = () => { error = ''; schedule(); draw(); };
        }
        return;
    }
    panel.insertAdjacentHTML('beforeend', `<div class="worked-status ${response.proof.status === 'checked' ? 'checked' : ''}" role="status">${escape(response.proof.message)}</div>
        <details class="worked-assumptions"><summary>Model, signs, and verification scope</summary><p>${escape(response.assumptions)}</p><p>${escape(response.conventions)}</p><p>${escape(response.proof.scope)}</p><p class="small">Course references: ${response.sources.map(escape).join(' · ')}</p><button id="download-proof">Download Lean source</button> <button id="download-proof-project">Download VS Code proof project</button></details>
        <div class="method-tabs" role="group" aria-label="Solution method">${[['sections', 'Method of sections'], ['integration', 'Double integration'], ['area', 'Moment-area theorems'], ['virtual', 'Principle of virtual work'], ['superposition', 'Method of superposition']].map(([id, label]) => `<button data-method="${id}" class="${id === method ? 'active' : ''}" aria-pressed="${id === method}">${label}</button>`).join('')}</div><article class="worked-steps">${steps()}</article>`);
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
    if (expanded && context.connected && !pending) timer = setTimeout(() => { void fetchSolution(); }, 650);
}

async function fetchSolution(): Promise<void> {
    if (pending || !expanded || !context.connected) return;
    const key = snapshot;
    const payload = { model: structuredClone(context.model), section: context.section };
    pending = true;
    error = '';
    try {
        const result = await context.request(payload);
        if (key === snapshot) response = result;
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
        error = '';
        // New practice questions require an explicit reveal. Exploration
        // refreshes automatically after geometry, load, or section edits.
        if (next.practice) expanded = false;
        draw();
        schedule();
    } else if (modeChanged || !document.getElementById('toggle-worked')) draw();
}
