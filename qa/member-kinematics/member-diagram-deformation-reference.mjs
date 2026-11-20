/** Independent slope and transverse-displacement values for the student
 * cases. The piece coordinate t increases from the first face to the last.
 * Coefficients are in rad and m respectively. Distances are in metres.
 */
import { exact, add, subtract, multiply, divide, negative, sqrt, bounds }
    from '../inclined-diagram/member-diagram-inclined-reference.mjs';

const zero = exact(0), one = exact(1), half = divide(one, exact(2));
const EI = exact(20000);
const q = (numerator, denominator) => divide(exact(numerator), exact(denominator));

function evaluate(coefficients, coordinate) {
    return coefficients.reduceRight((value, coefficient) => add(coefficient, multiply(value, coordinate)), zero);
}

/** Express a polynomial in x=origin+length*t, retaining exact rational
 * coefficients whenever the original geometry permits.
 */
function substitute(coefficients, origin, length) {
    let substituted = [coefficients.at(-1)];
    for (let index = coefficients.length - 2; index >= 0; index--) {
        const next = Array(substituted.length + 1).fill(zero);
        for (const [power, coefficient] of substituted.entries()) {
            next[power] = add(next[power], multiply(origin, coefficient));
            next[power + 1] = add(next[power + 1], multiply(length, coefficient));
        }
        next[0] = add(next[0], coefficients[index]);
        substituted = next;
    }
    return substituted;
}

function describePiece(length, a, b, theta, v) {
    const start = multiply(length, a), end = multiply(length, b);
    return { a, b, start, end, theta, v };
}

function writtenPiece(piece) {
    return { a: bounds(piece.a)[0], b: bounds(piece.b)[0], start: bounds(piece.start), end: bounds(piece.end),
        theta: piece.theta.map(bounds), v: piece.v.map(bounds) };
}

function row(piece, index, field, side, t, min = false, max = false, knownValue) {
    const x = side === 'flat' ? [piece.start[0], piece.end[1]] :
        add(piece.start, multiply(subtract(piece.end, piece.start), t));
    const value = knownValue ?? evaluate(piece[field], side === 'flat' ? zero : t);
    return { index, field, side, t: bounds(t), x: bounds(x), value: bounds(value), min, max };
}

function report(length, pieces, candidates) {
    return { length: bounds(length), pieces: pieces.map(writtenPiece), candidates };
}

/** Fixed portal B–C under full-span w=6−2x kN/m, or a 4/3 load edit.
 * z=x−3 and D=1557/563. Integrate M=z³/3−Dz using the actual
 * frame end rotation and displacement. The integration constants give
 * theta=[z⁴/12−Dz²/2+C]/EI and v=[z⁵/60−Dz³/6+Cz]/EI.
 */
export function portalDeformation(edited = false) {
    const length = exact(6), D = q(1557, 563), C = q(6489, 2252);
    const scale = edited ? q(4, 3) : one;
    const scaled = coefficients => coefficients.map(c => multiply(divide(c, EI), scale));
    const theta = scaled([C, zero, negative(divide(D, exact(2))), zero, q(1, 12)]);
    const v = scaled([zero, C, zero, negative(divide(D, exact(6))), zero, q(1, 60)]);
    const piece = describePiece(length, zero, one, substitute(theta, exact(-3), length), substitute(v, exact(-3), length));
    const thetaOffset = sqrt(multiply(exact(3), D));
    const thetaMin = multiply(divide(subtract(C, multiply(q(3, 4), multiply(D, D))), EI), scale);
    const thetaMax = multiply(divide(C, EI), scale);
    const inner = sqrt(subtract(multiply(exact(9), multiply(D, D)), multiply(exact(12), C)));
    const vOffset = sqrt(subtract(multiply(exact(3), D), inner));
    const thetaT = divide(thetaOffset, length), vT = divide(vOffset, length);
    return report(length, [piece], [
        row(piece, 0, 'theta', 'start', zero),
        row(piece, 0, 'theta', 'interior', subtract(half, thetaT), true, false, thetaMin),
        row(piece, 0, 'theta', 'interior', half, false, true, thetaMax),
        row(piece, 0, 'theta', 'interior', add(half, thetaT), true, false, thetaMin),
        row(piece, 0, 'theta', 'end', one),
        row(piece, 0, 'v', 'start', zero),
        row(piece, 0, 'v', 'interior', subtract(half, vT), true, false, evaluate(v, negative(vOffset))),
        row(piece, 0, 'v', 'interior', add(half, vT), false, true, evaluate(v, vOffset)),
        row(piece, 0, 'v', 'end', one),
    ]);
}

/** Simply supported uniform-load example. V=18−6x and M=18x−3x².
 * Enforce v(0)=v(6)=0 when integrating to obtain the additive rotation.
 */
export function pinnedUniformDeformation() {
    const length = exact(6);
    const theta = [exact(-54), zero, exact(9), exact(-1)].map(c => divide(c, EI));
    const v = [zero, exact(-54), zero, exact(3), q(-1, 4)].map(c => divide(c, EI));
    const piece = describePiece(length, zero, one, substitute(theta, zero, length), substitute(v, zero, length));
    return report(length, [piece], [
        row(piece, 0, 'theta', 'start', zero, true),
        row(piece, 0, 'theta', 'end', one, false, true),
        row(piece, 0, 'v', 'start', zero, false, true),
        row(piece, 0, 'v', 'interior', half, true, false, q(-81, 16000)),
        row(piece, 0, 'v', 'end', one, false, true),
    ]);
}

/** Fixed/free 4 m beam. Uniform upward q=6 kN/m, downward tip P=16
 * kN and +20 kN m tip couple produce M=3x²−8x+4. The slope
 * x(x−2)²/EI has an interior repeated zero that is no extremum of v.
 */
export function repeatedDisplacementRoot() {
    const length = exact(4);
    const theta = [zero, exact(4), exact(-4), one].map(c => divide(c, EI));
    const v = [zero, zero, exact(2), q(-4, 3), q(1, 4)].map(c => divide(c, EI));
    const piece = describePiece(length, zero, one, substitute(theta, zero, length), substitute(v, zero, length));
    return report(length, [piece], [
        row(piece, 0, 'theta', 'start', zero, true),
        row(piece, 0, 'theta', 'interior', q(1, 6)),
        row(piece, 0, 'theta', 'interior', half, true),
        row(piece, 0, 'theta', 'end', one, false, true),
        row(piece, 0, 'v', 'start', zero, true),
        row(piece, 0, 'v', 'interior', half, false, false, q(1, 15000)),
        row(piece, 0, 'v', 'end', one, false, true),
    ]);
}

/** Fixed–fixed two-span beam with 10 kN down at B and no joint couple.
 * Each 4 m span has a constant signed shear of magnitude 5 kN. AB starts
 * with M=T−20, then reaches T at B. Reflection gives BC from AB.
 */
export function cardinalJointDeformation(mode, member) {
    const transmission = { rigid: exact(10), hinge: zero, spring5000: q(20, 3), spring2500: exact(5) }[mode];
    if (!transmission) throw Error('Unknown joint benchmark');
    const reverse = member === 'BC';
    if (!reverse && member !== 'AB') throw Error('Select AB or BC');
    const length = exact(4);
    const initialMoment = subtract(transmission, exact(20));
    const theta = [zero, initialMoment, q(5, 2)].map(c => divide(c, EI));
    const v = [zero, zero, divide(initialMoment, exact(2)), q(5, 6)].map(c => divide(c, EI));
    const origin = reverse ? length : zero, step = reverse ? negative(length) : length;
    const angle = substitute(reverse ? theta.map(negative) : theta, origin, step);
    const piece = describePiece(length, zero, one, angle, substitute(v, origin, step));
    const rows = [
        row(piece, 0, 'theta', 'start', zero, reverse && mode === 'rigid', !reverse || mode === 'hinge'),
        row(piece, 0, 'theta', 'end', one, reverse || mode === 'hinge', !reverse && mode === 'rigid'),
        row(piece, 0, 'v', 'start', zero, reverse, !reverse),
        row(piece, 0, 'v', 'end', one, !reverse, reverse),
    ];
    // In the hinged limit the critical angle lies at a member end.
    if (mode !== 'hinge') {
        const t = divide(negative(initialMoment), exact(20));
        rows.push(row(piece, 0, 'theta', 'interior', reverse ? subtract(one, t) : t, !reverse, reverse));
    }
    const result = report(length, [piece], rows);
    result.jointRotation = bounds(evaluate(piece.theta, reverse ? zero : one));
    result.jointDisplacement = bounds(evaluate(piece.v, reverse ? zero : one));
    return result;
}

/** Rigid inclined cantilever under a pure +20 kN m tip couple, or the
 * inclined BC of a spring cantilever with horizontal AB, k=5000 kN m/rad.
 * The spring case has u_y(B)=1/125 m, theta_AB(B)=1/250 rad and
 * theta_BC(B)=1/125 rad. AB has zero axial movement.
 */
export function inclinedCoupleDeformation(reversed = false, spring = false) {
    const length = sqrt(exact(20));
    const thetaStart = spring ? q(1, 125) : zero;
    const vStart = spring ? divide(q(4, 125), length) : zero;
    const slopeCoefficients = [thetaStart, divide(length, exact(1000))];
    const transverseCoefficients = [vStart, multiply(length, thetaStart), q(1, 100)];
    const theta = reversed ? substitute(slopeCoefficients, one, exact(-1)) : slopeCoefficients;
    const v = reversed ? substitute(transverseCoefficients, one, exact(-1)).map(negative) : transverseCoefficients;
    const piece = describePiece(length, zero, one, theta, v);
    return report(length, [piece], [
        row(piece, 0, 'theta', 'start', zero, !reversed, reversed),
        row(piece, 0, 'theta', 'end', one, reversed, !reversed),
        row(piece, 0, 'v', 'start', zero, true),
        row(piece, 0, 'v', 'end', one, false, true),
    ]);
}

/** Inclined released BC with C on a vertical roller. The 10 kN midspan
 * force gives reactions of 5 kN, v_B=−8/(375L), v_C=L/3750 and zero
 * net axial extension. Integrate each triangular moment piece from B.
 */
export function inclinedHingeDeformation() {
    const length = sqrt(exact(20));
    const vB = divide(q(-8, 375), length), vC = divide(length, exact(3750));
    const thetaMid = q(1, 750), thetaOffset = divide(length, exact(8000));
    const thetaB = subtract(thetaMid, thetaOffset);
    const mid = subtract(add(vB, divide(length, exact(1500))), q(1, 1200));
    const left = describePiece(length, zero, half, [thetaB, zero, thetaOffset],
        [vB, multiply(divide(length, exact(2)), thetaB), zero, q(1, 2400)]);
    const right = describePiece(length, half, one, [thetaMid, divide(length, exact(4000)), negative(thetaOffset)],
        [mid, divide(length, exact(1500)), q(1, 800), q(-1, 2400)]);
    const candidates = ['theta', 'v'].flatMap(field => [
        row(left, 0, field, 'start', zero, true),
        row(left, 0, field, 'end', one, false, false, field === 'theta' ? thetaMid : mid),
        row(right, 1, field, 'start', zero),
        row(right, 1, field, 'end', one, false, true, field === 'theta' ? add(thetaMid, thetaOffset) : vC),
    ]);
    return report(length, [left, right], candidates);
}

export function unloadedDeformation() {
    const length = exact(6), piece = describePiece(length, zero, one, [zero], [zero]);
    return report(length, [piece], ['theta', 'v'].flatMap(field => [
        row(piece, 0, field, 'start', zero, true, true),
        row(piece, 0, field, 'flat', [zero[0], one[1]], true, true),
        row(piece, 0, field, 'end', one, true, true),
    ]));
}
