/** Untrusted real-geometry enclosure proposals, using rational arithmetic only.
 * The formal checker must independently validate the source and containment chain. */
import { type Fraction, fraction, zero, one, integer, add, sub, mul, div, neg, absolute, compare } from './frame-rational.js';
import { IntervalArithmetic, type RationalInterval } from './frame-interval.js';

/** Canonical rational degree class; no floating angle or rank tolerance. */
export function degreeClass(angle: Fraction, period: 180 | 360): Fraction {
    const denominator = angle.d * BigInt(period);
    const remainder = ((angle.n % denominator) + denominator) % denominator;
    return fraction(remainder, angle.d);
}

export function memberGeometry(arithmetic: IntervalArithmetic, dx: Fraction, dy: Fraction) {
    const squaredLength = add(mul(dx, dx), mul(dy, dy));
    if (compare(squaredLength, zero) <= 0) throw Error('Malformed geometry: coincident member endpoints.');
    const length = arithmetic.squareRoot(arithmetic.bounds(squaredLength));
    if (compare(length.lower, zero) <= 0) throw Error('Inconclusive: positive member length not resolved.');
    return { length, cosine: arithmetic.divide(arithmetic.bounds(dx), length),
        sine: arithmetic.divide(arithmetic.bounds(dy), length) };
}

/** Mathlib's pinned Real.pi_gt_d20/pi_lt_d20 bracket. Its finite width is
 * retained in every result; refinement cannot silently remove that uncertainty. */
const piLower = fraction(314159265358979323846n, 100000000000000000000n);
const piUpper = fraction(314159265358979323847n, 100000000000000000000n);

export function degreeAxes(arithmetic: IntervalArithmetic, sourceAngle: Fraction): {
    cosine: RationalInterval; sine: RationalInterval;
} {
    const angle = degreeClass(sourceAngle, 360);
    // Exact cardinal identities retain zero coefficients without uncertainty.
    for (let quadrant = 0; quadrant < 4; quadrant++) {
        if (compare(angle, integer(90 * quadrant)) === 0) return {
            cosine: arithmetic.bounds(integer([1, 0, -1, 0][quadrant])),
            sine: arithmetic.bounds(integer([0, 1, 0, -1][quadrant])),
        };
    }
    const reduced = compare(angle, integer(180)) > 0 ? sub(angle, integer(360)) : angle;
    const halvings = arithmetic.bits / 4;
    const pi = arithmetic.bounds(piLower, piUpper);
    const radians = arithmetic.multiply(arithmetic.bounds(div(reduced, integer(180))), pi);
    const x = arithmetic.divide(radians, arithmetic.bounds(fraction(1n << BigInt(halvings))));
    const magnitude = compare(absolute(x.lower), absolute(x.upper)) > 0 ? absolute(x.lower) : absolute(x.upper);
    if (compare(magnitude, one) > 0) throw Error('Inconclusive: small-angle bound premise failed.');
    const squared = arithmetic.multiply(x, x);
    const cubed = arithmetic.multiply(squared, x);
    // Real.sin_bound and Real.cos_bound both use 5|x|^4/96 for |x|<=1.
    const error = mul(fraction(5n, 96n), mul(mul(magnitude, magnitude), mul(magnitude, magnitude)));
    const remainder = arithmetic.bounds(neg(error), error);
    let sine = arithmetic.add(arithmetic.subtract(x, arithmetic.divide(cubed, arithmetic.bounds(integer(6)))), remainder);
    let cosine = arithmetic.add(arithmetic.subtract(arithmetic.bounds(one), arithmetic.divide(squared, arithmetic.bounds(integer(2)))), remainder);
    for (let step = 0; step < halvings; step++) {
        const doubledSine = arithmetic.multiply(arithmetic.bounds(integer(2)), arithmetic.multiply(sine, cosine));
        const doubledCosine = arithmetic.subtract(arithmetic.multiply(cosine, cosine), arithmetic.multiply(sine, sine));
        sine = doubledSine;
        cosine = doubledCosine;
    }
    return { sine, cosine };
}
