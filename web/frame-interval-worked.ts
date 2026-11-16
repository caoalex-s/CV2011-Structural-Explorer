/** Numerical teaching substitutions kept separate from accepted interval data. */
import { analyse } from './engine.js';
import type { EvidenceQuery } from './model-evidence.js';
import type { IntervalValues } from './frame-interval-result.js';
import { validateIntervalFrame } from './frame-interval-model.js';
import { bindIntervalDisplay, renderIntervalValues } from './frame-interval-display.js';
import { symbols, expression } from './frame-worked-rules.js';
import { math, numberLatex } from './math.js';

/** Reconstruct a numerical explanation from the captured source. This record
 * has no acceptance state and its estimates inherit no enclosure guarantee. */
export function createIntervalExplanation(input: unknown, query: EvidenceQuery, values: IntervalValues) {
    bindIntervalDisplay(input, query, values);
    const model = validateIntervalFrame(input, query);
    const selected = model.members.find(member => member.id === query.member)!;
    const a = model.nodes.find(node => node.id === selected.a)!;
    const b = model.nodes.find(node => node.id === selected.b)!;
    const sourceSpans = model.members.flatMap(member => {
        const cuts = new Set([0, 1]);
        for (const support of model.supports) if (support.member === member.id) cuts.add(support.t);
        for (const load of model.loads) if (load.member === member.id) {
            cuts.add(load.t);
            if (load.kind === 'distributed') cuts.add(load.end);
        }
        const ordered = [...cuts].sort((left, right) => left - right);
        return ordered.slice(0, -1).map((from, index) => ({ member: member.id, from, to: ordered[index + 1] }));
    });
    const spans = sourceSpans.filter(span => span.member === selected.id &&
        span.from <= query.parameter && query.parameter <= span.to);
    const span = query.cutSide === 'left' ? spans[0] : spans[spans.length - 1];
    const analysis = analyse(model);
    if (analysis.status !== 'stable') throw Error('Numerical explanation could not resolve this checked model.');
    if (analysis.elements.length !== sourceSpans.length || sourceSpans.some(source =>
        !analysis.elements.some(element => element.member === source.member && element.t0 === source.from && element.t1 === source.to)))
        throw Error('Numerical explanation uses a different source cut inventory.');
    // The numerical overview merges sufficiently close cuts. Refuse to borrow
    // its segment whenever that changes the exact source interval selected here.
    const segment = analysis.elements.find(element => element.member === selected.id &&
        element.t0 === span.from && element.t1 === span.to);
    if (!segment) throw Error('Numerical explanation uses a different source cut interval.');
    const first = segment.samples[0];
    let verticalStart = 0, verticalEnd = 0;
    for (const load of model.loads) {
        if (load.member !== selected.id || load.kind !== 'distributed' || load.t > span.from || load.end < span.to) continue;
        const intensity = (parameter: number) => load.fy + (load.qEnd - load.fy) * (parameter - load.t) / (load.end - load.t);
        verticalStart += intensity(span.from);
        verticalEnd += intensity(span.to);
    }
    const { c, s, length } = segment;
    const slope = (verticalEnd - verticalStart) / length;
    const inputs: Record<string, number> = {
        x: length * (query.parameter - span.from) / (span.to - span.from), L: length,
        c, s, EA: selected.EA, EI: selected.EI,
        p: s * verticalStart, q: c * verticalStart, dp: s * slope, dq: c * slope,
        a1: -first.N, a2: first.V, a3: -first.M,
        u0: c * first.ux + s * first.uy, v0: -s * first.ux + c * first.uy, theta0: first.rotation,
    };
    if (Object.values(inputs).some(value => !Number.isFinite(value))) throw Error('Nonfinite numerical explanation.');
    return { version: 'inclined-explanation/1', evidence: 'explanatory-numerical' as const,
        member: selected.id, query: structuredClone(query), span, inputs,
        geometry: { ax: a.x, ay: a.y, bx: b.x, by: b.y, length: Math.hypot(b.x - a.x, b.y - a.y) } };
}

export function renderIntervalExplanation(explanation: ReturnType<typeof createIntervalExplanation>, values: IntervalValues): string {
    const { inputs, span } = explanation;
    const rounded = (value: number) => numberLatex(value);
    const units: Record<string, string> = { x: 'm', L: 'm', c: '', s: '', EA: 'kN', EI: 'kN m²',
        p: 'kN/m', q: 'kN/m', dp: 'kN/m²', dq: 'kN/m²', a1: 'kN', a2: 'kN', a3: 'kN m',
        u0: 'm', v0: 'm', theta0: 'rad' };
    const fields = ['N', 'V', 'M', 'rotation', 'ux', 'uy'];
    const labels = ['N', 'V', 'M', '\\theta', 'u_x', 'u_y'];
    const rules = fields.map((id, index) => `<div class="worked-equation" data-evidence="explanatory-numerical">
        ${math(`${labels[index]}=${expression(id, key => symbols[key])}.`, true)}
        <p>Rounded numerical substitution:</p>
        ${math(`${labels[index]}\\approx ${expression(id, key => `\\left(${rounded(inputs[key])}\\right)`)}.`, true)}</div>`).join('');
    return `<p>The accepted intervals establish a unique equilibrium solution for the captured drawing. The substitutions below come from a separate numerical calculation and explain the field equations. Their rounded inputs do not inherit the accuracy guarantee of the exact midpoints.</p>
      <h3>1. Geometry and equilibrium</h3>
      <p>Local x follows the member from its first node to its second node. The direction cosines c and s rotate local translations into global coordinates. For the displacement vector d, the columns of P span all motions permitted by the supports:</p>
      ${math('\\mathbf d=P\\mathbf z,\\qquad A=P^{\\mathsf T}KP,\\qquad \\mathbf b=P^{\\mathsf T}\\mathbf F,\\qquad A\\mathbf z=\\mathbf b.', true)}
      <p>Here K is the assembled stiffness matrix and F is the assembled load vector. The checker encloses the real member lengths and support directions before checking the reduced system. Positive elastic energy together with uniqueness establishes stability within this linear model.</p>
      <h3>2. Selected load segment</h3>
      <p>The selected one-sided segment extends from t = ${span.from} to t = ${span.to}. Its local coordinate x is measured from the segment start. Distributed axial and transverse loads have the forms ${math('p(x)=p_0+k_px')} and ${math('q(x)=q_0+k_qx')}.</p>
      <table><thead><tr><th>Operand</th><th>Numerical estimate</th><th>Unit</th></tr></thead><tbody>${Object.entries(inputs).map(([key, value]) => `<tr><td>${math(symbols[key])}</td><td>${math('\\approx ' + rounded(value))}</td><td>${units[key]}</td></tr>`).join('')}</tbody></table>
      <p>The starting element actions are a₁, a₂, and a₃. Starting displacements u₀ and v₀ are local translations, and θ₀ is the starting rotation. Equilibrium and integration of the axial and bending strains give the following section fields:</p>
      <h3>3. Field equations and numerical substitutions</h3>${rules}
      <h3>4. Accepted intervals and exact midpoint accuracy</h3>${renderIntervalValues(values)}`;
}
