/** Human-readable course methods, tied to an exact model/section snapshot. */
import type { Model } from './engine.js';

interface Equation { label: string; mathml: string; exact: string; unit: string }
interface WorkedResponse {
    title: string;
    section: string;
    length: string;
    assumptions: string;
    conventions: string;
    supports: { a: string; b: string };
    equilibrium: Equation[];
    actions: { position: string; fx: string; fy: string; couple: string; arm: string; included: boolean }[];
    pieces: { interval: string; forces: Equation[]; displacements: Equation[] }[];
    constants: Equation[];
    selected: Equation[];
    momentArea: { title: string; equation: Equation; terms: Equation[] }[];
    thetaLeft: Equation;
    virtual: { reactions: Equation[]; rows: { interval: string; equations: Equation[] }[]; result: Equation };
    superposition: Equation[];
    proof: { status: string; message: string; scope: string; sha256: string; source: string; groups: Record<string, string[]> };
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

/** Accept presentation MathML only, even when a separately hosted API is used. */
function safeMath(markup: string): string {
    const document = new DOMParser().parseFromString(markup, 'application/xml');
    const allowed = new Set(['math', 'mrow', 'mi', 'mn', 'mo', 'mfrac', 'msup', 'msub', 'msubsup', 'mfenced', 'msqrt', 'mroot', 'mtext']);
    for (const node of Array.from(document.querySelectorAll('*'))) {
        if (!allowed.has(node.localName) || node.namespaceURI !== 'http://www.w3.org/1998/Math/MathML') return '';
        for (const attribute of Array.from(node.attributes)) {
            if (!['xmlns', 'mathvariant', 'open', 'close', 'separators'].includes(attribute.name)) node.removeAttribute(attribute.name);
        }
    }
    return new XMLSerializer().serializeToString(document.documentElement);
}

function equations(rows: Equation[]): string {
    return rows.map(row => `<div class="worked-equation"><span>${escape(row.label)} =</span>${safeMath(row.mathml) || escape(row.exact)}<small>${escape(row.unit)}</small></div>`).join('');
}

function proofLabel(groups: string[]): string {
    if (!response) return '';
    const count = groups.reduce((sum, group) => sum + (response!.proof.groups[group]?.length || 0), 0);
    return `<span class="method-proof ${response.proof.status === 'checked' ? 'checked' : ''}">${response.proof.status === 'checked' ? `Lean checked · ${count} statements` : 'Symbolic result · Lean not checked'}</span>`;
}

function steps(): string {
    const data = response!;
    const intervals = (field: 'forces' | 'displacements') => data.pieces.map((piece, i) => `<details class="worked-interval" ${i === 0 ? 'open' : ''}><summary>Interval ${i + 1}: ${escape(piece.interval)} m</summary>${equations(piece[field])}</details>`).join('');
    const selected = `<h3>At the selected section: xₛ = ${escape(data.section)} m</h3>${equations(data.selected)}`;
    if (method === 'sections') return `
        ${proofLabel(['equilibrium', 'partition', 'sections', 'diagrams', 'jumps', 'ends', 'readout'])}
        <h3>1. Find the support reactions</h3>
        <p>Replace the supports by their reactions. Keep each force at its application point and each couple at its stated sign. Let a = ${escape(data.supports.a)} m and b = ${escape(data.supports.b)} m denote the left and right support coordinates.</p>
        <div class="worked-rule">ΣFₓ = 0 &nbsp; · &nbsp; Rₗ + Rᵣ + F = 0<br>ΣMₐ = 0: Rᵣ(b − a) + T − aF = 0</div>${equations(data.equilibrium)}
        <h3>2. Cut the beam and balance the left free body</h3>
        <p>For each interval, include actions to the left of the cut. A force contributes its magnitude multiplied by its distance from the cut. Integrate only the part of a distributed load lying on this free body.</p>
        <div class="worked-rule">N(x) = −ΣFₓ<br>V(x) = ΣFᵧ + ∫q(s) ds<br>M(x) = ΣFᵧ(x − xᵢ) − ΣCᵢ + ∫q(s)(x − s) ds</div>
        <details><summary>Point actions on the selected free body, including reactions</summary><div class="worked-table"><table class="data-table"><thead><tr><th>xᵢ (m)</th><th>Fₓ (kN)</th><th>Fᵧ (kN)</th><th>C (kN m)</th><th>Arm (m)</th><th>Included</th></tr></thead><tbody>${data.actions.map(a => `<tr><td>${escape(a.position)}</td><td>${escape(a.fx)}</td><td>${escape(a.fy)}</td><td>${escape(a.couple)}</td><td>${escape(a.arm)}</td><td>${a.included ? 'Yes' : 'No'}</td></tr>`).join('')}</tbody></table></div></details>
        <h3>3. Build the diagrams interval by interval</h3>
        <p>The following expressions determine the full diagrams. Between point actions, V′ = q and M′ = V. At a point force, ΔV = Fᵧ and ΔN = −Fₓ. A counterclockwise couple gives ΔM = −C. Changing the plotted tension/compression side leaves these signed equations unchanged.</p>${intervals('forces')}${selected}`;
    if (method === 'integration') return `
        ${proofLabel(['integration', 'conditions', 'continuity', 'readout'])}
        <h3>1. Start with the bending-moment equation</h3><p>The course relation EI v″ = M connects the moment diagram to curvature. Integrate each interval once to obtain the rotation θ = v′ and again to obtain the vertical displacement v. Retain the integration constants until the support and continuity conditions have been imposed.</p>
        <div class="worked-rule">θ(x) = ∫ M(x)/(EI) dx + constant<br>v(x) = ∫ θ(x) dx + constant</div>
        <h3>2. Impose continuity and the support conditions</h3><p>Here B(x) is the twice-integrated moment function with continuity imposed at every interval boundary and B(0) = B′(0) = 0. Write v(x) = B(x) + C₁x + C₀. The two support conditions determine the remaining constants.</p>
        <div class="worked-rule">v(a) = v(b) = 0<br>C₁ = −(B(b) − B(a))/(b − a)<br>C₀ = −B(a) − aC₁<br>v⁻ = v⁺ and θ⁻ = θ⁺ at each interior boundary</div>${equations(data.constants)}
        <h3>3. Read the displacement and rotation functions</h3>${intervals('displacements')}${selected}`;
    if (method === 'area') return `
        ${proofLabel(['moment_area'])}
        <h3>1. Measure area under M/(EI)</h3><p>The first moment-area theorem gives the change in slope between two points. The second theorem gives the deviation from the tangent at the starting point. This tangential deviation differs from the absolute displacement when the starting tangent is inclined.</p>
        <div class="worked-rule">θ(c) − θ(a) = ∫ₐᶜ M(x)/(EI) dx<br>t(c/a) = ∫ₐᶜ (c − x)M(x)/(EI) dx<br>v(c) = v(a) + (c − a)θ(a) + t(c/a)</div>
        <h3>2. Determine the tangent at the left support</h3><p>Both supports have zero vertical displacement. Applying the second theorem between them gives θ(a) = −t(b/a)/(b − a). Use this tangent when evaluating displacement at the selected section. Integrals to a point on the left overhang have reversed limits.</p>${equations([data.thetaLeft])}
        <h3>3. Add the interval contributions</h3>${data.momentArea.map(row => `<details class="worked-interval" open><summary>${escape(row.title)}</summary>${equations(row.terms)}${equations([row.equation])}</details>`).join('')}${selected}`;
    if (method === 'virtual') return `
        ${proofLabel(['virtual_work'])}
        <h3>1. Apply a virtual unit force</h3><p>Remove the real loads and apply an upward force of 1 kN at xₛ = ${escape(data.section)} m. Keep the support conditions unchanged. Find its reactions and virtual bending moment m using the same x-coordinate as the real moment M.</p>${equations(data.virtual.reactions)}
        <h3>2. Evaluate the internal virtual work</h3><div class="worked-rule">(1 kN) v(xₛ) = ∑ ∫ m(x)M(x)/(EI) dx</div><p>Split the integral wherever the real or virtual moment expression changes. Each integral below has units of kN m. Divide the sum by the virtual force of 1 kN to obtain displacement in metres.</p>
        ${data.virtual.rows.map(row => `<details class="worked-interval" open><summary>${escape(row.interval)} m</summary>${equations(row.equations)}</details>`).join('')}
        <h3>3. Interpret the sign</h3>${equations([data.virtual.result])}<p>A negative result means displacement opposite to the upward virtual force. The certificate tests whether this integral equals the displacement obtained by double integration.</p>`;
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
        <details class="worked-assumptions"><summary>Model, signs, and verification scope</summary><p>${escape(response.assumptions)}</p><p>${escape(response.conventions)}</p><p>${escape(response.proof.scope)}</p><p class="small">Course references: ${response.sources.map(escape).join(' · ')}</p><button id="download-proof">Download this Lean certificate</button></details>
        <div class="method-tabs" role="group" aria-label="Solution method">${[['sections', 'Section equilibrium'], ['integration', 'Double integration'], ['area', 'Moment-area'], ['virtual', 'Virtual work'], ['superposition', 'Superposition']].map(([id, label]) => `<button data-method="${id}" class="${id === method ? 'active' : ''}" aria-pressed="${id === method}">${label}</button>`).join('')}</div><article class="worked-steps">${steps()}</article>`);
    panel.querySelectorAll<HTMLButtonElement>('[data-method]').forEach(button => button.onclick = () => { method = button.dataset.method!; draw(); });
    document.getElementById('download-proof')!.onclick = () => {
        const url = URL.createObjectURL(new Blob([response!.proof.source], { type: 'text/plain' }));
        const link = document.createElement('a');
        link.href = url;
        link.download = `WorkedBeam-${response!.proof.sha256.slice(0, 12)}.lean`;
        link.click();
        setTimeout(() => URL.revokeObjectURL(url), 1000);
    };
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
    } else if (!document.getElementById('toggle-worked')) draw();
}
