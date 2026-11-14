/** Untrusted recovery of affine loaded fields from enclosed global motion.
 * Local signs and one-sided segment selection match the existing exact path. */
import { binary64, compare, sub, div, integer, zero } from './frame-rational.js';
import { IntervalArithmetic, type RationalInterval } from './frame-interval.js';
import { intervalDot } from './frame-interval-solve.js';
import type { compileIntervalFrame } from './frame-interval-model.js';

export function recoverIntervalFields(arithmetic: IntervalArithmetic,
    frame: ReturnType<typeof compileIntervalFrame>, motion: RationalInterval[]) {
    if (motion.length !== frame.force.length) throw Error('Malformed motion dimensions.');
    const member = frame.model.members.findIndex(item => item.id === frame.query.member);
    const parameter = binary64(frame.query.parameter);
    const segment = frame.segments.find(item => item.member === member &&
        (frame.query.cutSide === 'right'
            ? compare(item.from, parameter) <= 0 && compare(parameter, item.to) < 0
            : compare(item.from, parameter) < 0 && compare(parameter, item.to) <= 0));
    if (!segment) throw Error('Malformed query: no owned segment at the selected limit.');
    const global = [...motion.slice(3 * segment.start, 3 * segment.start + 3),
        ...motion.slice(3 * segment.end, 3 * segment.end + 3)];
    const local = segment.transform.map(row => intervalDot(arithmetic, row, global));
    const actions = segment.localStiffness.map((row, i) =>
        arithmetic.subtract(intervalDot(arithmetic, row, local), segment.localForce[i]));
    const constant = (value: number) => arithmetic.bounds(integer(value));
    const times = arithmetic.multiply.bind(arithmetic);
    const over = arithmetic.divide.bind(arithmetic);
    const minus = arithmetic.negate.bind(arithmetic);
    const sum = (terms: RationalInterval[]) => terms.reduce((total, term) => arithmetic.add(total, term), arithmetic.bounds(zero));
    const term = (coefficient: RationalInterval, power: RationalInterval, denominator: number) => over(times(coefficient, power), constant(denominator));
    const x = times(segment.length, arithmetic.bounds(div(sub(parameter, segment.from), sub(segment.to, segment.from))));
    const xSquared = times(x, x), xCubed = times(xSquared, x), xFourth = times(xSquared, xSquared);
    const axialLoad = times(segment.sine, arithmetic.bounds(segment.vertical));
    const transverseLoad = times(segment.cosine, arithmetic.bounds(segment.vertical));
    const globalSlope = over(arithmetic.bounds(sub(segment.verticalEnd, segment.vertical)), segment.length);
    const axialSlope = times(segment.sine, globalSlope), transverseSlope = times(segment.cosine, globalSlope);
    const N = sum([minus(actions[0]), minus(times(axialLoad, x)), minus(term(axialSlope, xSquared, 2))]);
    const V = sum([actions[1], times(transverseLoad, x), term(transverseSlope, xSquared, 2)]);
    const M = sum([minus(actions[2]), times(actions[1], x), term(transverseLoad, xSquared, 2), term(transverseSlope, xCubed, 6)]);
    const u = arithmetic.add(local[0], over(sum([times(minus(actions[0]), x),
        minus(term(axialLoad, xSquared, 2)), minus(term(axialSlope, xCubed, 6))]), arithmetic.bounds(segment.EA)));
    const v = sum([local[1], times(local[2], x), over(sum([term(minus(actions[2]), xSquared, 2),
        term(actions[1], xCubed, 6), term(transverseLoad, xFourth, 24),
        term(transverseSlope, times(xFourth, x), 120)]), arithmetic.bounds(segment.EI))]);
    const rotation = arithmetic.add(local[2], over(sum([times(minus(actions[2]), x), term(actions[1], xSquared, 2),
        term(transverseLoad, xCubed, 6), term(transverseSlope, xFourth, 24)]), arithmetic.bounds(segment.EI)));
    const ux = arithmetic.subtract(times(segment.cosine, u), times(segment.sine, v));
    const uy = arithmetic.add(times(segment.sine, u), times(segment.cosine, v));
    return [N, V, M, rotation, ux, uy];
}
