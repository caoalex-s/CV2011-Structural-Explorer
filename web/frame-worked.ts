/** Teaching records reconstructed from an accepted frame packet.
 * This is a presentation layer, never an acceptance predicate. Intermediate
 * arithmetic has explanatory status even when it reproduces a checked result.
 */
import type { Model } from './engine.js';
import type { EvidenceQuery } from './model-evidence.js';
import type { Rational } from './portal-candidate.js';
import type { CheckedFrameValues } from './frame-result.js';
import { compileFrame, recoverFrame } from './frame-candidate.js';
import { type Fraction, binary64, fraction, encoded, mul, sub, div, dot, compare, equal } from './frame-rational.js';
import { symbols, expression } from './frame-worked-rules.js';

export const workedRuleVersion = 'frame-worked/1';
export interface WorkedBinding {
    revision: number; request: number; bindings: unknown; artifact: unknown;
    bundle: unknown; inputDigest: unknown; packetDigest: string;
}
export interface WorkedStep {
    id: string; rule: string; version: typeof workedRuleVersion;
    dependencies: string[]; inputs: Record<string, Rational>;
    inputUnits: Record<string, string>;
    evidence: 'explanatory-rule'; predicate: string;
    symbolicExpression?: string; exactSubstitution?: string;
    result?: { value: Rational; unit: string; packetReference: string; evidence: 'verified-result' };
}
export interface FrameWorkedSolution {
    version: typeof workedRuleVersion; binding: WorkedBinding; model: Model; query: EvidenceQuery;
    values: CheckedFrameValues; steps: WorkedStep[];
    interval?: { from: Rational; to: Rational; member: string; values: Record<string, Rational> };
}
const decode = (value: Rational): Fraction => fraction(BigInt(value.numerator), BigInt(value.denominator));
const named = (values: Record<string, Fraction>): Record<string, Rational> =>
    Object.fromEntries(Object.entries(values).map(([key, value]) => [key, encoded(value)]));
const inputUnits: Record<string, string> = { x: 'm', L: 'm', c: '1', s: '1', EA: 'kN', EI: 'kN m²',
    p: 'kN/m', q: 'kN/m', a1: 'kN', a2: 'kN', a3: 'kN m', u0: 'm', v0: 'm', theta0: 'rad' };
function freeze<T>(value: T): T {
    if (value && typeof value === 'object') {
        Object.values(value).forEach(freeze);
        Object.freeze(value);
    }
    return value;
}

/** Capture current source and accepted values, then reconstruct explanations.
 * The caller must have checked packet digest, runtime identity and request token.
 * No invocation here can turn a candidate or a JavaScript equality into a proof.
 */
export function createFrameWorked(model: Model, query: EvidenceQuery, values: CheckedFrameValues,
    binding: WorkedBinding): FrameWorkedSolution {
    const frame = compileFrame(model, query);
    if (values.query.member !== query.member || values.query.cutSide !== query.cutSide ||
        !equal(decode(values.query.parameter), binary64(query.parameter)) ||
        values.query.quantity !== query.quantity || values.query.units !== query.units ||
        values.query.signConvention !== query.signConvention) throw Error('Worked query differs from accepted query.');
    if (values.points.length !== frame.points.length) throw Error('Worked point map differs from accepted point map.');
    frame.points.forEach((point, index) => {
        const accepted = values.points[index];
        const id = point.owner === 'node' ? frame.model.nodes[point.index].id : frame.model.members[point.index].id;
        if (accepted.owner !== point.owner || accepted.id !== id || accepted.index !== point.index ||
            !equal(decode(accepted.parameter), point.t) || !equal(decode(accepted.x), point.x) || !equal(decode(accepted.y), point.y))
            throw Error('Worked point ownership differs from accepted source.');
    });
    const report: FrameWorkedSolution = structuredClone({ version: workedRuleVersion, binding,
        model: frame.model, query, values, steps: [] });
    if (values.kind === 'mechanism') return freeze(report);
    const motion = values.points.flatMap(point => point.motion.map(decode));
    const recovered = recoverFrame(frame, motion);
    if (recovered.some((value, index) => !equal(value, decode(values.readouts[index]))))
        throw Error('Explanatory recovery differs from accepted values.');
    // Check this presentation's assembly and grouped residual reconstruction.
    // These diagnostics do not extend the compiled acceptance scope.
    frame.stiffness.forEach((row, index) => {
        const residual = sub(dot(row, motion), frame.force[index]);
        const reaction = values.points[Math.floor(index / 3)].reaction?.[index % 3];
        if (!reaction || !equal(residual, decode(reaction))) throw Error('Explanatory reaction differs from accepted value.');
    });
    const memberIndex = frame.model.members.findIndex(member => member.id === query.member);
    const t = binary64(query.parameter);
    const intervals = frame.segments.filter(segment => segment.member === memberIndex &&
        compare(segment.from, t) <= 0 && compare(t, segment.to) <= 0);
    const segment = query.cutSide === 'left' ? intervals[0] : intervals[intervals.length - 1];
    const local = segment.indices.map((index, i) => mul(segment.signs[i], motion[index]));
    const actions = segment.stiffness.map((row, i) => sub(dot(row, local), segment.force[i]));
    const x = mul(segment.length, div(sub(t, segment.from), sub(segment.to, segment.from)));
    const inputs = named({ x, L: segment.length, c: segment.c, s: segment.s, EA: segment.EA, EI: segment.EI,
        p: mul(segment.s, segment.vertical), q: mul(segment.c, segment.vertical),
        a1: actions[0], a2: actions[1], a3: actions[2], u0: local[0], v0: local[1], theta0: local[2] });
    report.interval = { from: encoded(segment.from), to: encoded(segment.to), member: query.member, values: inputs };
    const step = (id: string, rule: string, predicate: string, dependencies: string[], data = inputs): WorkedStep =>
        ({ id, rule, version: workedRuleVersion, dependencies, inputs: data,
            inputUnits: Object.fromEntries(Object.keys(data).map(key => [key, inputUnits[key]])),
            evidence: 'explanatory-rule', predicate });
    report.steps.push(step('equilibrium', 'constrained-stiffness', 'RationalFrame.Stability.checked_unique', ['source', 'packet.motion'], {}));
    report.steps.push(step('reactions', 'grouped-residual', 'RationalFrame.Reactions.checked_grouped_reactions', ['equilibrium', 'packet.reactions'], {}));
    const units = ['kN', 'kN', 'kN m', 'rad', 'm', 'm'];
    ['N', 'V', 'M', 'rotation', 'ux', 'uy'].forEach((id, index) => report.steps.push({
        ...step(id, 'loaded-field-' + id, 'RationalFrame.Recovery.checked_readouts', ['source', 'packet.motion', 'selected-interval']),
        symbolicExpression: expression(id, key => symbols[key]),
        exactSubstitution: expression(id, key => {
            const value = inputs[key];
            const latex = value.denominator === '1' ? value.numerator : `\\frac{${value.numerator}}{${value.denominator}}`;
            return `\\left(${latex}\\right)`;
        }),
        result: { value: structuredClone(values.readouts[index]), unit: units[index],
            packetReference: `readouts[${index}]`, evidence: 'verified-result' },
    }));
    return freeze(report);
}

/** Export/render validation detects changed step claims or dependencies. This
 * is a presentation-integrity check, explicitly not a compiled equation check. */
export function validateFrameWorked(report: FrameWorkedSolution): void {
    const expected = createFrameWorked(report.model, report.query, report.values, report.binding);
    if (JSON.stringify(expected) !== JSON.stringify(report)) throw Error('Worked explanation or evidence claims changed.');
}
