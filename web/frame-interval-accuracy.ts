/** Exact arithmetic for the proposed output-accuracy policy. Passing this
 * arithmetic gate alone does not establish formal containment or acceptance. */
import { type Fraction, fraction, zero, add, sub, mul, div, absolute, compare } from './frame-rational.js';
import type { RationalInterval } from './frame-interval.js';

export type EnclosedQuantity = 'N' | 'V' | 'M' | 'rotation' | 'ux' | 'uy' | 'Rx' | 'Ry' | 'Mz';
export const enclosureAccuracyVersion = 'frame-enclosure-accuracy/1';
const relative = fraction(1n, 100000000n);
const force = { absolute: fraction(1n, 1000000n), unit: 'kN' };
const moment = { absolute: fraction(1n, 1000000n), unit: 'kN m' };
const displacement = { absolute: fraction(1n, 1000000000n), unit: 'm' };
const policies = {
    N: force, V: force, M: moment, rotation: { absolute: fraction(1n, 10000000000n), unit: 'rad' },
    ux: displacement, uy: displacement, Rx: force, Ry: force, Mz: moment,
};

/** Inputs must already use the named protocol units. No display conversion is
 * permitted inside the gate. The midpoint radius is not an engine-error bound. */
export function enclosureAccuracy(quantity: EnclosedQuantity, interval: RationalInterval, estimate?: Fraction) {
    if (compare(interval.lower, interval.upper) > 0) throw Error('Malformed interval: reversed bounds.');
    const policy = policies[quantity];
    const midpoint = div(add(interval.lower, interval.upper), fraction(2n));
    const radius = div(sub(interval.upper, interval.lower), fraction(2n));
    const difference = sub(absolute(midpoint), radius);
    const lowerMagnitude = compare(difference, zero) > 0 ? difference : zero;
    const targetRadius = add(policy.absolute, mul(relative, lowerMagnitude));
    let estimateError: Fraction | undefined;
    if (estimate !== undefined) {
        const fromLower = absolute(sub(estimate, interval.lower));
        const fromUpper = absolute(sub(estimate, interval.upper));
        estimateError = compare(fromLower, fromUpper) > 0 ? fromLower : fromUpper;
    }
    return { version: enclosureAccuracyVersion, quantity, unit: policy.unit, interval, midpoint, radius,
        absoluteTolerance: policy.absolute, relativeTolerance: relative, targetRadius,
        meetsTarget: compare(radius, targetRadius) <= 0, estimate, estimateError };
}
