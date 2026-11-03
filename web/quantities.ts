/** Course extrema and point evaluations from the exact beam service. */
import { equationHtml, compactEquationHtml, symbolicEquationHtml, math, rationalLatex } from './math.js';
import type { Equation } from './math.js';

interface Extremum {
    kind: 'minimum' | 'maximum' | 'absolute';
    value: number;
    lower: string;
    upper: string;
    exact: boolean;
    x: string;
    xApprox: number;
    xExact: boolean;
    side: string;
    piece: number;
    plateau: boolean;
    substitution: Equation;
    coordinate?: Equation;
    governing?: Equation;
    stationary?: Equation;
    isStationary?: boolean;
    compactSubstitution?: Equation;
}
interface QuantitySummary {
    field: string;
    title: string;
    symbol: string;
    unit: string;
    stationaryRule: string;
    extrema: Extremum[];
    roots: { interval: number; equation: Equation; coordinateLatex: string | null; lower: string; upper: string; approx: number; candidateValue: number; valueLatex: string | null }[];
    cells: number;
    group: string;
}
interface QuantityPoint {
    labels: string[];
    x: string;
    xApprox: number;
    side: string;
    piece: number;
    values: Record<string, number>;
    substitutions: Equation[];
}
export interface KeyQuantities {
    summaries: QuantitySummary[];
    points: QuantityPoint[];
}

const escape = (text: string) => text.replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]!));
const number = (value: number) => value === 0 ? '0' : Number(value.toPrecision(7)).toString();
const position = (value: { xApprox: number; side: string }) => `${number(value.xApprox)}${value.side ? `<sup>${value.side === '-' ? '−' : '+'}</sup>` : ''}`;
const extremumPosition = (value: Extremum) => value.xExact
    ? math(`${rationalLatex(value.x)}${value.side ? `^{${value.side}}` : ''}`)
    : position(value);
const names = { minimum: 'Minimum signed value', maximum: 'Maximum signed value', absolute: 'Maximum magnitude' };
const rangeSymbol = (extremum: Extremum, symbol: string) => extremum.kind === 'absolute'
    ? String.raw`\max|${symbol}|`
    : `${extremum.kind === 'minimum' ? String.raw`\min` : String.raw`\max`} ${symbol}`;

function valueHtml(extremum: Extremum, unit: string): string {
    const value = extremum.exact ? math(rationalLatex(extremum.lower)) : `≈ ${number(extremum.value)}`;
    return `${value} <span class="quantity-unit">${escape(unit)}</span>`;
}

function boundsHtml(extremum: Extremum, symbol: string): string {
    if (extremum.exact) return '<p class="small">The lower and upper bounds coincide. This value is exact.</p>';
    return `<p class="small">The reported value is approximate. Its exact rational enclosure is</p>${math(`${rationalLatex(extremum.lower)}\\le ${symbol}\\le ${rationalLatex(extremum.upper)}.`, true)}`;
}

interface DerivationContext {
    equilibrium: Equation[];
    selected: Equation[];
}

/** The first view follows the short calculation a student would write down. */
export function renderKeyQuantities(data: KeyQuantities, proofBadge: (groups: string[]) => string, context: DerivationContext): string {
    const highlights = data.summaries.filter(summary => ['M', 'theta', 'v'].includes(summary.field));
    const traces = highlights.map((summary, index) => {
        const peak = summary.extrema.find(row => row.kind === 'absolute')!;
        const stationary = peak.isStationary || summary.roots.some(root =>
            root.interval === peak.piece && Math.abs(root.approx - peak.xApprox) < 1e-7);
        const method = summary.field === 'M'
            ? `<p>Balance the support reactions, then cut the beam.</p>${context.equilibrium.slice(3, 5).map(row => symbolicEquationHtml({ ...row, labelLatex: row.labelLatex.split('=')[0].trim(), symbolicLabelLatex: row.symbolicLabelLatex?.split('=')[0].trim() })).join('')}`
            : `<p>Integrate the moment equation and apply the support and continuity conditions.</p>${math(String.raw`EI v''=M,\qquad \theta=v',\qquad v(a)=v(b)=0`, true)}`;
        const search = stationary
            ? `<p>Solve ${math(summary.stationaryRule)} within the interval, then compare with its endpoint limits.</p>${peak.stationary ? symbolicEquationHtml(peak.stationary) : ''}`
            : `<p>Compare the member ends, interval boundaries, and stationary points. ${peak.plateau ? 'This value is constant on the governing interval.' : 'An endpoint or interval boundary governs.'}</p>`;
        return `<details class="quantity-trace" ${index === 0 ? 'open' : ''}>
            <summary><span>Maximum ${math(`|${summary.symbol}|`)}</span><strong>${peak.exact && String(peak.value) === peak.lower ? '' : '≈ '}${number(peak.value)} ${escape(summary.unit)}</strong><span>at x ${peak.xExact ? '=' : '≈'} ${position(peak)} m</span></summary>
            <div class="quantity-calculation"><section class="derivation-step"><h3>1. Derive the response</h3>${method}${peak.governing ? symbolicEquationHtml(peak.governing) : ''}</section>
            <section class="derivation-step"><h3>2. Locate the governing point</h3>${search}<p class="small">Interval ${peak.piece}; location for the current loading.</p>${peak.coordinate ? compactEquationHtml(peak.coordinate) : ''}</section>
            <section class="derivation-step derivation-evaluation"><h3>3. Substitute and evaluate</h3>${compactEquationHtml(peak.compactSubstitution || peak.substitution)}
            ${math(`\\max|${summary.symbol}| ${peak.exact ? '=' : '\\approx'} ${peak.exact ? rationalLatex(peak.lower) : number(peak.value)}\\;\\mathrm{${summary.unit.replaceAll(' ', '\\,')}}`, true)}
            ${proofBadge([summary.group])}</section></div></details>`;
    }).join('');
    return `<p class="small">Symbols → numbers → result. The governing locations refer to the current loads; changing their relative magnitudes can move an extremum.</p>${traces}
        <details class="worked-interval"><summary>Values at the selected section</summary>${proofBadge(['readout'])}${context.selected.map(compactEquationHtml).join('')}</details>
        <details class="worked-interval"><summary>All point values, signed extrema, and proof details</summary>${renderQuantityDetails(data, proofBadge)}</details>`;
}

function renderQuantityDetails(data: KeyQuantities, proofBadge: (groups: string[]) => string): string {
    const highlights = data.summaries.filter(summary => ['M', 'theta', 'v'].includes(summary.field));
    const cards = highlights.map(summary => {
        const peak = summary.extrema.find(row => row.kind === 'absolute')!;
        return `<div class="quantity-card"><small>Maximum ${math(`|${summary.symbol}|`)}</small><strong>${valueHtml(peak, summary.unit)}</strong><span>At ${math('x')} ${peak.xExact ? '=' : '≈'} ${extremumPosition(peak)} m${peak.plateau ? ' · constant on this interval' : ''}</span></div>`;
    }).join('');
    const rows = data.points.map(point => `<tr><td>${escape(point.labels.join(' · '))}</td><td>${position(point)}</td>${['N', 'V', 'M', 'theta', 'v'].map(field => `<td>${number(point.values[field])}</td>`).join('')}</tr>`).join('');
    const details = data.summaries.map(summary => `<details class="worked-interval">
        <summary>${escape(summary.title)} ${math(summary.symbol)}: extrema and derivation</summary>
        ${proofBadge([summary.group])}
        <h3>1. Locate candidate sections</h3>
        <p>Compare both member ends, interval boundaries, and both limits at a jump. Within a smooth interval, solve ${math(summary.stationaryRule)}. A zero derivative throughout an interval means that the response is constant there.</p>
        ${summary.roots.length ? summary.roots.map(root => `<div class="quantity-root"><p>Interval ${root.interval}:</p>${equationHtml(root.equation)}${math(root.coordinateLatex ? `x=${root.coordinateLatex}\\,\\mathrm m.` : `${rationalLatex(root.lower)}<x<${rationalLatex(root.upper)}\\,\\mathrm m.`, true)}<p>Substitution gives ${math(summary.symbol)} ${root.valueLatex ? `= ${math(root.valueLatex)}` : `≈ ${number(root.candidateValue)}`} ${escape(summary.unit)} at this stationary point.</p></div>`).join('') : '<p class="small">There are no isolated stationary points inside the intervals. Compare their endpoint limits.</p>'}
        <h3>2. Evaluate and compare signed values</h3>
        <p>The minimum and maximum signed values distinguish direction. The maximum magnitude compares their absolute values. These extrema and coordinates apply to the current parameter values. Changing the load amplitudes can change the governing point. The symbolic line evaluates the displayed comparison point and does not assert that it remains an extremum for all parameter values.</p>
        ${summary.extrema.map(extremum => `<section class="quantity-result"><h4>${names[extremum.kind]}</h4><p>${valueHtml(extremum, summary.unit)} at ${math('x')} ${extremum.xExact ? '=' : '≈'} ${extremumPosition(extremum)} m, interval ${extremum.piece}${extremum.plateau ? ' (one representative point of a constant interval)' : ''}.</p>${equationHtml(extremum.substitution)}${boundsHtml(extremum, rangeSymbol(extremum, summary.symbol))}</section>`).join('')}
        <h3>3. Check the whole curve</h3>
        <p>The range calculation covers every polynomial interval, including one-sided limits. On each subinterval, substitute ${math('x=a+(b-a)t')} and express the polynomial in a Bernstein basis. Its nonnegative basis functions sum to one on ${math('0\\le t\\le1')}, placing the polynomial between its smallest and largest coefficients.</p>
        <p>Lean checks the interval coverage, polynomial basis conversions, coefficient inequalities, and values at comparison points. This result uses ${summary.cells} subinterval${summary.cells === 1 ? '' : 's'}. The real-domain convex-hull theorem and isolation of irrational stationary roots remain outside the Lean formalisation; the coefficient bounds cover the whole curve independently of the root search.</p>
    </details>`).join('');
    return `${proofBadge([...data.summaries.map(summary => summary.group), 'key_points'])}
        <h3>Maximum magnitudes</h3><div class="quantity-cards">${cards}</div>
        <p class="small">The coordinate ${math('x')} is measured from the left member end. A superscript − or + identifies the left or right limit. One location is shown when several points share the same extremum. Slopes are in milliradians (${math('1\\,\\mathrm{mrad}=10^{-3}\\,\\mathrm{rad}')}); vertical displacement is positive upward. These beam results use the exact piecewise equations, independently of the canvas sampling.</p>
        <h3>Values at points of interest</h3>
        <p>Supports, load positions, distributed-load boundaries, midspan, and the selected cut are included. Move the section slider to evaluate another point. Separate rows preserve discontinuities at concentrated forces and couples. Numerical columns are rounded; the point derivations retain exact fractions.</p>
        <div class="worked-table"><table class="data-table quantity-table"><thead><tr><th>Point</th><th>x (m)</th><th>N (kN)</th><th>V (kN)</th><th>M (kN m)</th><th>θ (mrad)</th><th>v (mm)</th></tr></thead><tbody>${rows}</tbody></table></div>
        <details class="worked-interval"><summary>Derive the point values</summary>${proofBadge(['key_points'])}<p>Choose the polynomial for the indicated interval and substitute the coordinate. Multiplication by 1000 converts radians to milliradians and metres to millimetres.</p>${data.points.map(point => `<details><summary>${escape(point.labels.join(' · '))}: x = ${position(point)} m</summary><p>Use interval ${point.piece}.</p>${point.substitutions.map(equationHtml).join('')}</details>`).join('')}</details>
        <h3>Derive and bound the extrema</h3>${details}
        <p class="small">Use <b>Model, signs, and verification scope</b> above to download the Lean source or VS Code project. It contains these point evaluations and range-certificate statements together with the beam derivation.</p>`;
}
