/** Untrusted inverse-residual proposals for an already enclosed reduced system.
 * Numerical inversion supplies witnesses only. No acceptance or stability status
 * is returned here; the compiled checker must recompute every bound. */
import { type Fraction, zero, one, fraction, binary64, add, sub, div, absolute, compare } from './frame-rational.js';
import { IntervalArithmetic, type RationalInterval } from './frame-interval.js';

export type IntervalMatrix = RationalInterval[][];
const midpoint = (value: RationalInterval) => div(add(value.lower, value.upper), fraction(2n));
const magnitude = (value: RationalInterval) => compare(absolute(value.lower), absolute(value.upper)) > 0
    ? absolute(value.lower) : absolute(value.upper);

/** Partial-pivot floating inversion is deliberately outside the trusted boundary. */
function approximateInverse(matrix: IntervalMatrix): Fraction[][] {
    const count = matrix.length;
    const work = matrix.map((row, i) => [...row.map(value => {
        const middle = midpoint(value);
        const number = Number(middle.n) / Number(middle.d);
        if (!Number.isFinite(number)) throw Error('Inconclusive: numerical inverse scale is not finite.');
        return number;
    }), ...Array.from({ length: count }, (_, j) => i === j ? 1 : 0)]);
    for (let column = 0; column < count; column++) {
        let pivot = column;
        for (let row = column + 1; row < count; row++)
            if (Math.abs(work[row][column]) > Math.abs(work[pivot][column])) pivot = row;
        if (!Number.isFinite(work[pivot][column]) || work[pivot][column] === 0)
            throw Error('Inconclusive: numerical inverse proposal failed.');
        [work[column], work[pivot]] = [work[pivot], work[column]];
        const divisor = work[column][column];
        for (let j = 0; j < 2 * count; j++) work[column][j] /= divisor;
        for (let row = 0; row < count; row++) if (row !== column) {
            const multiplier = work[row][column];
            for (let j = 0; j < 2 * count; j++) work[row][j] -= multiplier * work[column][j];
        }
    }
    return work.map(row => row.slice(count).map(value => {
        if (!Number.isFinite(value)) throw Error('Inconclusive: inverse proposal is not finite.');
        return binary64(value);
    }));
}

export function intervalDot(arithmetic: IntervalArithmetic, left: RationalInterval[], right: RationalInterval[]) {
    if (left.length !== right.length) throw Error('Malformed interval vector dimensions.');
    let sum = arithmetic.bounds(zero);
    for (let i = 0; i < left.length; i++) sum = arithmetic.add(sum, arithmetic.multiply(left[i], right[i]));
    return sum;
}

/** Norm coordinates are numerical values in the protocol's fixed m/rad units.
 * There is no hidden matrix scaling. Any future scaling must be checked explicitly. */
export function proposeIntervalSolution(arithmetic: IntervalArithmetic, matrix: IntervalMatrix, force: RationalInterval[]) {
    const count = matrix.length;
    if (count > 48 || force.length !== count || matrix.some(row => row.length !== count))
        throw Error('Malformed or oversized reduced system.');
    const inverse = approximateInverse(matrix);
    const intervalInverse = inverse.map(row => row.map(value => arithmetic.bounds(value)));
    const middleForce = force.map(value => arithmetic.bounds(midpoint(value)));
    const estimate = intervalInverse.map(row => midpoint(intervalDot(arithmetic, row, middleForce)));
    const intervalEstimate = estimate.map(value => arithmetic.bounds(value));
    const residual = matrix.map((row, i) => arithmetic.subtract(force[i], intervalDot(arithmetic, row, intervalEstimate)));
    const preconditionedResidual = intervalInverse.map(row => intervalDot(arithmetic, row, residual));
    let eta = zero, contraction = zero;
    for (let i = 0; i < count; i++) {
        const residualMagnitude = magnitude(preconditionedResidual[i]);
        if (compare(residualMagnitude, eta) > 0) eta = residualMagnitude;
        let rowSum = zero;
        for (let j = 0; j < count; j++) {
            const product = intervalDot(arithmetic, intervalInverse[i], matrix.map(row => row[j]));
            const defect = arithmetic.subtract(arithmetic.bounds(i === j ? one : zero), product);
            rowSum = add(rowSum, magnitude(defect));
        }
        if (compare(rowSum, contraction) > 0) contraction = rowSum;
    }
    if (compare(contraction, one) >= 0) throw Error('Inconclusive: inverse-residual contraction was not established.');
    const errorRadius = div(eta, sub(one, contraction));
    const enclosure = estimate.map(value => arithmetic.bounds(sub(value, errorRadius), add(value, errorRadius)));
    return { inverse, estimate, contraction, eta, errorRadius, enclosure, precisionBits: arithmetic.bits };
}
