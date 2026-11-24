/** Predictions belong to the drawn portal and the checked whole-member report. */
import { endConnection } from './engine.js';
import type { Model } from './engine.js';
import { absolute, add, binary64, compare, equal, integer, one, sub } from './frame-rational.js';
import type { Fraction } from './frame-rational.js';
import { element as $ } from './ui.js';

export const portalExercise = new URLSearchParams(location.search).get('exercise') === 'portal-absolute-moment';
export const exerciseStep = 'portal_absolute_moment';
export const exerciseStorage = 'cv2011-portal-absolute-moment/v1';

// The checker interprets each raw coordinate as its exact binary64 value.
// Subtracting in JavaScript can make two unequal column heights look equal.
function hasExactSpan(start: number, end: number, metres: number): boolean {
    try {
        return equal(sub(binary64(end), binary64(start)), integer(metres));
    } catch {
        return false; // Coordinates outside the rational budget cannot establish symmetry.
    }
}

function portalBeam(model: Model) {
    if (model.nodes.length !== 4 || model.members.length !== 3 || model.supports.length !== 2 || model.loads.length !== 1) return;
    const load = model.loads[0];
    const beam = model.members.find(m => m.id === load.member);
    if (!beam || load.direction !== undefined || load.kind !== 'distributed' || load.fx !== 0 || load.mz !== 0 || !(load.fy * load.qEnd < 0) ||
        !(0 <= load.t && load.t < load.end && load.end <= 1)) return;
    const nodes = new Map(model.nodes.map(node => [node.id, node]));
    const b = nodes.get(beam.a), c = nodes.get(beam.b);
    if (!b || !c || b.y !== c.y || !hasExactSpan(b.x, c.x, 6)) return;
    if (model.members.some(m => m.EA !== 2000000 || m.EI !== 20000 || (['a', 'b'] as const).some(end =>
        Object.values(endConnection(model, m, end)).some(rule => rule !== 'rigid')))) return;
    for (const top of [beam.a, beam.b]) {
        const column = model.members.find(m => m !== beam && (m.a === top || m.b === top));
        if (!column) return;
        const bottom = column.a === top ? 1 : 0;
        const foot = nodes.get(bottom === 1 ? column.b : column.a);
        const head = nodes.get(top);
        if (!foot || !head || foot.x !== head.x || !hasExactSpan(foot.y, head.y, 4) ||
            !model.supports.some(s => s.kind === 'fixed' && s.member === column.id && s.t === bottom)) return;
    }
    return beam;
}

const rational = (value: string): Fraction => {
    const [n, d] = value.split('/').map(BigInt);
    return { n, d };
};
function decimalValue(value: Fraction): number {
    const numerator = value.n < 0n ? -value.n : value.n;
    if (numerator === 0n) return 0;
    const digits = numerator.toString(), denominator = value.d.toString();
    const leading = (s: string) => Number(s[0] + '.' + s.slice(1, 17));
    return (value.n < 0n ? -1 : 1) * leading(digits) / leading(denominator) * 10 ** (digits.length - denominator.length);
}

/** Keep the submitted decimal distance exact at the inclusive tolerance boundary. */
function distances(text: string): Fraction[] | undefined {
    if (text.length > 256) return;
    const values: Fraction[] = [];
    for (const part of text.split(',')) {
        const match = /^([+]?)(\d*)(?:\.(\d*))?(?:e([+-]?\d+))?$/i.exec(part.trim());
        if (!match || !(match[2] || match[3])) return;
        const places = (match[3]?.length || 0) - Number(match[4] || '0');
        if (Math.abs(places) > 400) return;
        const digits = BigInt(match[2] + (match[3] || ''));
        const value = { n: digits * 10n ** BigInt(Math.max(-places, 0)), d: 10n ** BigInt(Math.max(places, 0)) };
        if (value.n > 6n * value.d) return;
        values.push(value);
    }
    return values.sort(compare);
}


function peaks(rows: HTMLElement, model: Model) {
    const candidates = Array.from(rows.querySelectorAll<HTMLElement>('[data-field="M"][data-candidate]'))
        .filter(row => row.dataset.min === 'true' || row.dataset.max === 'true')
        .map(row => {
            const data = row.dataset;
            const y0 = rational(data.yLow!), y1 = rational(data.yHigh!);
            const magnitudes = [absolute(y0), absolute(y1)].sort(compare);
            const low = y0.n <= 0n && y1.n >= 0n ? { n: 0n, d: 1n } : magnitudes[0];
            const xLow = rational(data.xLow!), xHigh = rational(data.xHigh!);
            return {
                low, high: magnitudes[1], xLow, xHigh, x0: decimalValue(xLow), x1: decimalValue(xHigh),
                moment: (decimalValue(y0) + decimalValue(y1)) / 2, flat: data.side === 'flat'
            };
        });
    const possible = candidates.filter(a => !candidates.some(b => compare(b.low, a.high) > 0)).sort((a, b) => a.x0 - b.x0);
    // Adjacent pieces may report the same boundary. Only equal singleton
    // rationals establish identity; overlapping location boxes can be distinct.
    const distinct = possible.filter((p, i) => !equal(p.xLow, p.xHigh) ||
        !possible.slice(0, i).some(q => equal(q.xLow, q.xHigh) && equal(q.xLow, p.xLow)));
    const load = model.loads[0];
    const symmetric = equal(add(binary64(load.t), binary64(load.end)), one) && load.fy === -load.qEnd;
    const resolved = distinct.length === 1 || (distinct.length === 2 && symmetric && distinct[0].moment * distinct[1].moment < 0);
    return { distinct, resolved: resolved && distinct.every(p => !p.flat && p.x1 - p.x0 < 0.001) };
}

/** Show rounded substitutions while keeping the exact piece coefficients in
 * the checked table. Both report formats use distance measured from B. */
function substitutions(diagram: HTMLElement, model: Model): string[] {
    const load = model.loads[0];
    const lines: string[] = [];
    const display = (n: number) => String(Number(n.toPrecision(6))).replace('-', '−');
    function polynomial(values: number[]) {
        const terms: string[] = [];
        const powers = ['', 'ξ', 'ξ²', 'ξ³'];
        values.forEach((value, index) => {
            if (value === 0) return;
            const sign = value < 0 ? '−' : '+';
            const magnitude = Math.abs(value);
            const term = (index > 0 && magnitude === 1 ? '' : display(magnitude)) + powers[index];
            terms.push(terms.length ? ' ' + sign + ' ' + term : (value < 0 ? '−' : '') + term);
        });
        return terms.join('') || '0';
    }
    function value(text: string) { return decimalValue(rational(text)); }
    for (const piece of diagram.querySelectorAll<HTMLElement>('[data-piece]')) {
        const d = piece.dataset;
        const a = d.start ? value(d.start) : 6 * value(d.left!);
        const b = d.end ? value(d.end) : 6 * value(d.right!);
        const shear = d.shear?.split(',').map(value);
        const moment = d.moment?.split(',').map(value);
        const v0 = shear ? shear[0] : (value(d.vLow!) + value(d.vHigh!)) / 2;
        const m0 = moment ? moment[0] : (value(d.mLow!) + value(d.mHigh!)) / 2;
        const centre = (a + b) / 12;
        const loaded = centre > load.t && centre < load.end;
        const gradient = loaded ? (load.fy - load.qEnd) / (6 * (load.end - load.t)) : 0;
        const w0 = loaded ? -load.fy + gradient * (a - 6 * load.t) : 0;
        lines.push('For ' + display(a) + ' ≤ x ≤ ' + display(b) + ' m, take ξ = x − ' + display(a) + ' m. ' +
            'w(ξ) ≈ ' + polynomial([w0, gradient]) + ' kN/m, V(ξ) ≈ ' + polynomial([v0, -w0, -gradient / 2]) +
            ' kN and M(ξ) ≈ ' + polynomial([m0, v0, -w0 / 2, -gradient / 6]) + ' kN·m.');
    }
    return lines;
}

export function createMomentExercise(getModel: () => Model, selectBeam: (id: string) => void, refresh: () => void,
    history: () => { predictions: number; revealed: boolean }, adjust: (boundaries: { t: number; end: number }) => void, record: (event: string, answer: string, assisted: boolean) => void) {
    const panel = $('portal-exercise');
    panel.innerHTML = `<h2>Where does the largest |M| occur on BC?</h2>
    <p>Draw AB upwards 4 m, BC to the right 6 m, and CD downwards 4 m. For example, start at A (0, −2) m. Fix both bases and keep the joints rigid. Use EA = 2,000,000 kN and EI = 20,000 kN·m² for all three members.</p>
    <p>Apply a vertical distributed load over BC. In Properties set the downward-positive intensities to +6 kN/m at B and −6 kN/m at C. Measure x from B towards C.</p>
    <label>Predict every location of the largest bending-moment magnitude, in metres from B. Separate multiple locations with commas (tolerance 0.02 m).
    <input id="moment-prediction" maxlength="256" autocomplete="off"></label>
    <button id="moment-check">Check prediction</button> <button id="moment-reveal" disabled>Reveal worked solution</button>
    <p id="moment-feedback" role="status"></p><div id="moment-explanation"></div><div id="moment-adjustment"></div><p id="moment-progress"></p>
    <p>After checking the full-span load, change the intensities to +8 and −8 kN/m. Predict again. Then move the start to one-sixth of BC, keep the end at C, and recheck the peak locations.</p>`;
    const input = $<HTMLInputElement>('moment-prediction'), reveal = $<HTMLButtonElement>('moment-reveal');
    const feedback = $('moment-feedback'), explanation = $('moment-explanation');
    const key = exerciseStorage + '/prediction';
    let source = '', prediction = '', count = 0, revealed = false, exposed = false;
    let outcome: ReturnType<typeof peaks> | undefined;
    let working: string[] = [];
    function save() {
        sessionStorage.setItem(key, JSON.stringify({ source, prediction, count, exposed }));
    }
    function bind(binding: string) {
        if (binding === source) return;
        source = binding; prediction = ''; count = 0; exposed = false; revealed = false; outcome = undefined;
        try {
            const saved = JSON.parse(sessionStorage.getItem(key) || '{}');
            if (saved.source === binding) { prediction = saved.prediction; count = saved.count; exposed = saved.exposed; }
        } catch { /* A missing prediction starts a fresh drawing. */ }
        $('moment-adjustment').replaceChildren();
        save(); input.value = prediction; reveal.disabled = true; explanation.textContent = '';
        feedback.textContent = prediction ? 'Checking the prediction for this drawing…' : '';
        document.body.classList.add('moment-locked');
    }
    function grade() {
        if (!outcome || !prediction) return;
        reveal.disabled = false;
        if (!outcome.resolved) {
            feedback.textContent = 'The checked bounds leave the ordering of the candidate magnitudes unresolved. This prediction is ungraded.';
            return;
        }
        const answer = distances(prediction);
        if (!answer) return;
        const matches = answer.map((distance, index) => {
            const peak = outcome!.distinct[index];
            if (!peak) return 'outside';
            const lower = { n: 50n * distance.n - distance.d, d: 50n * distance.d };
            const upper = { n: 50n * distance.n + distance.d, d: 50n * distance.d };
            if (compare(lower, peak.xHigh) > 0 || compare(upper, peak.xLow) < 0) return 'outside';
            if (compare(lower, peak.xLow) <= 0 && compare(upper, peak.xHigh) >= 0) return 'inside';
            return 'overlap';
        });
        const sameCount = answer.length === outcome.distinct.length;
        if (sameCount && !matches.includes('outside') && matches.includes('overlap')) {
            feedback.textContent = 'The checked location interval crosses the 0.02 m tolerance boundary. This prediction is ungraded.';
            return;
        }
        const correct = sameCount && matches.every(match => match === 'inside');
        feedback.textContent = correct ? 'Correct for this drawing.' : 'Check the number and locations of the peaks. You can retry or reveal the worked solution.';
    }
    $('moment-check').onclick = () => {
        const beam = portalBeam(getModel());
        if (!beam) { feedback.textContent = 'Check the beam direction, dimensions, fixed bases, rigid connections, stiffnesses and sign-changing vertical load.'; return; }
        const value = input.value.trim();
        if (!distances(value)) {
            feedback.textContent = 'Enter one or more distances between 0 and 6 m.'; return;
        }
        selectBeam(beam.id);
        const prior = history();
        count = Math.max(count, prior.predictions) + 1; exposed ||= prior.revealed;
        prediction = value; input.value = value; save();
        record(count === 1 ? 'first_prediction' : 'retry', value, exposed);
        if (outcome) grade();
        else { feedback.textContent = 'Checking the whole-member extrema for this drawing…'; $('frame-generate').click(); }
    };
    reveal.onclick = () => {
        if (!outcome || !prediction) return;
        const revealedOnThisCheck = revealed;
        revealed = true;
        if (!revealedOnThisCheck) record('reveal', prediction, true);
        exposed = true; save(); document.body.classList.remove('moment-locked'); refresh();

        const locations = outcome.distinct.map(p => 'x ≈ ' + ((p.x0 + p.x1) / 2).toFixed(4) + ' m (M ≈ ' + p.moment.toFixed(4) + ' kN·m)').join(' and ');
        const heading = document.createElement('strong');
        heading.textContent = (outcome.resolved ? (outcome.distinct.length === 2 ?
            'Reflection about midspan reverses the load and moment signs. The two extrema have equal magnitude at ' :
            'The largest magnitude occurs at ') : 'The checked bounds leave these possible locations: ') + locations + '.';
        explanation.replaceChildren(heading);
        for (const line of ['Take downward w as positive. On each interval w = w₀ + gξ. Integrating dV/dx = −w gives V = V₀ − w₀ξ − gξ²/2. Integrating dM/dx = V gives M = M₀ + V₀ξ − w₀ξ²/2 − gξ³/6.',
            ...working, 'Set V = 0 to locate the interior moment extrema. Compare their absolute moments with those at the member ends and load boundaries in the checked table.']) {
            const paragraph = document.createElement('p'); paragraph.textContent = line; explanation.append(paragraph);
        }
    };
    function status(message: string) {
        if (!prediction || !/limit|timed out|inconclusive|failed|unavailable/i.test(message)) return;
        outcome = undefined; reveal.disabled = true; feedback.textContent = message + ' This prediction is ungraded.';
        const host = $('moment-adjustment'); host.replaceChildren();
        const load = getModel().loads[0];
        if (!load || !/limit|timed out/i.test(message)) return;
        const proposed = { t: Math.round(load.t * 8) / 8, end: Math.round(load.end * 8) / 8 };
        if (proposed.t >= proposed.end || proposed.t === load.t && proposed.end === load.end) return;
        const outOfRange = (['t', 'end'] as const).filter(key => {
            try { binary64(load[key]); return false; }
            catch { return true; }
        });
        const detail = outOfRange.map(key => 'The ' + (key === 't' ? 'start' : 'end') + ' fraction ' + load[key] +
            ' exceeds the exact input conversion budget. ').join('');
        const note = document.createElement('p'), button = document.createElement('button');
        note.textContent = detail + 'The checker reached its resource limit. You can try a different load extent. Start fraction ' + load.t + ' → ' + proposed.t + ', end fraction ' + load.end + ' → ' + proposed.end + '. Undo restores the original extent.';
        button.textContent = 'Apply these load boundaries'; button.onclick = () => adjust(proposed);
        host.append(note, button);
    }
    return {
        bind, status, get visible() { return revealed; }, checked(model: Model, member: string, rows: HTMLElement) {
            if (prediction && JSON.stringify(model) === JSON.stringify(getModel()) && portalBeam(model)?.id === member) {
                outcome = peaks(rows, model); working = substitutions(rows, model); grade();
                if (outcome.resolved) {
                    const load = model.loads[0];
                    const stages = JSON.parse(sessionStorage.getItem(exerciseStorage + '/stages') || '{}');
                    if (load.fy === -6 && load.qEnd === 6 && load.t === 0 && load.end === 1) stages.reference = true;
                    if (stages.reference && load.fy === -8 && load.qEnd === 8 && load.t === 0 && load.end === 1) stages.magnitude = true;
                    if (stages.magnitude && load.fy === -8 && load.qEnd === 8 && (load.t !== 0 || load.end !== 1)) stages.extent = true;
                    sessionStorage.setItem(exerciseStorage + '/stages', JSON.stringify(stages));
                    const finished = ['reference', 'magnitude', 'extent'].filter(stage => stages[stage]);
                    $('moment-progress').textContent = finished.length ? 'Drawings checked: ' + finished.join(', ') + '.' : '';
                }
            }
        }
    };
}
