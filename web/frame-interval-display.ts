/** Presentation of already accepted interval reports. No function here grants
 * checker status. Exact endpoints and midpoints remain available beside the
 * rounded values used to read the result at a glance. */
import type { EvidenceQuery } from './model-evidence.js';
import type { IntervalValues, IntervalReadout } from './frame-interval-result.js';
import type { Rational } from './portal-candidate.js';
import { roundedDecimal } from './portal-candidate.js';
import { binary64, encoded } from './frame-rational.js';
import { validateIntervalFrame } from './frame-interval-model.js';
import { nodeLabels, type Model } from './engine.js';
import { memberLabel, reactionSymbols } from './model-view.js';
import { math, rationalLatex } from './math.js';

const escape = (text: string) => text.replace(/[&<>"']/g, character =>
    ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[character]!));
const exact = (value: Rational): string => value.denominator === '1' ? value.numerator : `${value.numerator}/${value.denominator}`;
const same = (left: Rational, right: Rational): boolean =>
    left.numerator === right.numerator && left.denominator === right.denominator;

/** Check the displayed source identities without building a candidate matrix.
 * The original request digest and compiled ABI acceptance remain caller duties. */
export function bindIntervalDisplay(input: unknown, query: EvidenceQuery, values: IntervalValues): void {
    const model = validateIntervalFrame(input, query);
    if (values.query.member !== query.member || values.query.cutSide !== query.cutSide ||
        values.query.convention !== 1 || !same(values.query.parameter, encoded(binary64(query.parameter))))
        throw Error('Interval report query differs from the captured request.');
    const expected = model.nodes.map((node, index) =>
        ({ owner: 'node', index, id: node.id, parameter: encoded(binary64(0)) }));
    for (const [index, member] of model.members.entries()) {
        const cuts = new Set<number>();
        model.supports.filter(support => support.member === member.id).forEach(support => cuts.add(support.t));
        for (const load of model.loads) if (load.member === member.id) {
            cuts.add(load.t);
            if (load.kind === 'distributed') cuts.add(load.end);
        }
        for (const parameter of [...cuts].filter(value => value > 0 && value < 1).sort((a, b) => a - b))
            expected.push({ owner: 'member', index, id: member.id, parameter: encoded(binary64(parameter)) });
    }
    if (values.fields.length !== 6 || values.points.length !== expected.length)
        throw Error('Interval report dimensions differ from the captured request.');
    for (const [index, point] of values.points.entries()) {
        const source = expected[index];
        if (point.owner !== source.owner || point.index !== source.index || point.id !== source.id ||
            !same(point.parameter, source.parameter) || point.reactions.length !== 3)
            throw Error('Interval report point differs from the captured request.');
    }
}

/** Directed decimal rounding preserves enclosure using integer arithmetic. */
export function outwardDecimal(value: Rational, digits: number, direction: 'lower' | 'upper'): string {
    if (!Number.isInteger(digits) || digits < 0 || digits > 20) throw Error('Invalid display precision.');
    const numerator = BigInt(value.numerator), denominator = BigInt(value.denominator);
    if (denominator <= 0n) throw Error('Invalid display denominator.');
    const scale = 10n ** BigInt(digits);
    const scaled = numerator * scale;
    let rounded = scaled / denominator;
    if (scaled % denominator !== 0n) {
        if (direction === 'lower' && scaled < 0n) rounded--;
        if (direction === 'upper' && scaled > 0n) rounded++;
    }
    const magnitude = rounded < 0n ? -rounded : rounded;
    const decimal = digits ? `${magnitude / scale}.${String(magnitude % scale).padStart(digits, '0')}` : String(magnitude);
    return (rounded < 0n ? '-' : '') + decimal;
}

function row(label: string, unit: string, value: IntervalReadout, digits: number): string {
    const lower = outwardDecimal(value.lower, digits + 3, 'lower');
    const upper = outwardDecimal(value.upper, digits + 3, 'upper');
    return `<tr><th scope="row">${label} (${unit})</th>
      <td data-evidence="rounded-midpoint">≈ ${roundedDecimal(value.midpoint, digits)}</td>
      <td data-evidence="outward-enclosure">[${lower}, ${upper}]</td>
      <td><details><summary>Exact values</summary><p>Midpoint:<br><span data-evidence="exact-midpoint">${exact(value.midpoint)}</span></p>
      <p>Interval:<br><span data-evidence="exact-enclosure">[${exact(value.lower)}, ${exact(value.upper)}]</span></p></details></td></tr>`;
}

/** Render only parser-validated values after source binding and ABI acceptance. */
export function renderIntervalValues(values: IntervalValues, drawing?: Model): string {
    const nodes = drawing && nodeLabels(drawing);
    const members = drawing && new Map(drawing.members.map(member => [member.id, memberLabel(drawing, member)]));
    const fieldNames = [`Axial force ${math('N')}`, `Shear force ${math('V')}`, `Bending moment ${math('M')}`,
        `Rotation ${math('\\theta')}`, `Global horizontal displacement ${math('u_x')}`, `Global vertical displacement ${math('u_y')}`];
    const fieldUnits = ['kN', 'kN', 'kN m', 'rad', 'm', 'm'];
    const table = (rows: string) => `<table class="frame-interval-values"><thead><tr><th>Quantity</th>
      <th>Rounded midpoint</th><th>Outward decimal interval</th><th>Exact certificate values</th></tr></thead><tbody>${rows}</tbody></table>`;
    const fields = values.fields.map((value, index) => row(fieldNames[index], fieldUnits[index], value, index < 3 ? 6 : 10)).join('');
    const reactions = values.points.map(point => {
        const label = point.owner === 'node' ? `Node ${escape(nodes?.get(point.id) ?? point.id)}` :
            `Member ${escape(members?.get(point.id) ?? point.id)} at ${math('t=' + rationalLatex(exact(point.parameter)))}`;
        const symbols = reactionSymbols(point.owner === 'node' ? nodes?.get(point.id) : undefined);
        return `<h4>${label}</h4>${table(point.reactions.map((value, index) =>
            row('Grouped reaction ' + math(symbols[index]), index === 2 ? 'kN m' : 'kN', value, 6)).join(''))}`;
    }).join('');
    return `<p>Member ${escape(members?.get(values.query.member) ?? values.query.member)} is evaluated at ${math('t=' + rationalLatex(exact(values.query.parameter)))} using the ${values.query.cutSide} limit. Each interval contains the corresponding value of the original linear frame model. The exact midpoint is the reported approximation covered by the accuracy bound.</p>
      <p>For each exact midpoint ${math('m')} and real model value ${math('v')}, the checker establishes ${math(String.raw`|m-v|\le a+10^{-8}|v|`)}. The absolute tolerance ${math('a')} is ${math(String.raw`10^{-6}\,\mathrm{kN}`)} for forces, ${math(String.raw`10^{-6}\,\mathrm{kN}\,\mathrm{m}`)} for moments, ${math(String.raw`10^{-10}\,\mathrm{rad}`)} for rotation, and ${math(String.raw`10^{-9}\,\mathrm{m}`)} for displacement. Rounded midpoint values help read the tables and have additional decimal rounding error. Decimal interval endpoints are rounded outward to retain containment. Expand Exact values to inspect the original rational interval and midpoint.</p>
      <h3>Selected section</h3>${table(fields)}
      <h3>Grouped reactions</h3><p>Each row gives the total reaction at its source point. Supports attached to the same source point share this resultant. Geometric coincidence alone does not merge distinct source points. The report does not assign separate reactions to individual supports at one source point.</p>${reactions}`;
}
