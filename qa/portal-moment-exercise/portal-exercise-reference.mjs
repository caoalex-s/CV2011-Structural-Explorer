/** Independent stiffness and equilibrium reference for the teaching portal.
 * Loads use downward-positive kN/m and locations use metres from B to C.
 * Coefficients are exact rationals. Quadratic roots use outward enclosures.
 */
import { exact, add, subtract, multiply, divide, negative, sqrt, bounds }
    from './member-diagram-inclined-reference.mjs';

const zero = exact(0);
const one = exact(1);
const L = exact(6);
const H = exact(4);
const EA = exact(2000000);
const EI = exact(20000);

/** Interpret the selected browser number as its exact IEEE binary64 value. */
export function exactBrowserNumber(value) {
    if (!Number.isFinite(value)) throw new RangeError('Expected a finite browser number');
    const bytes = new DataView(new ArrayBuffer(8));
    bytes.setFloat64(0, Math.abs(value));
    const bits = bytes.getBigUint64(0);
    const storedExponent = Number(bits >> 52n);
    const significand = (bits & (2n ** 52n - 1n)) + (storedExponent === 0 ? 0n : 2n ** 52n);
    const exponent = Math.max(storedExponent, 1) - 1075;
    const signed = value < 0 ? -significand : significand;
    return exponent < 0 ? divide(exact(signed), exact(2n ** BigInt(-exponent))) :
        exact(signed * 2n ** BigInt(exponent));
}

function order(left, right) {
    const difference = BigInt(left[0]) * BigInt(right[1]) - BigInt(right[0]) * BigInt(left[1]);
    return difference < 0 ? -1 : Number(difference > 0);
}

function signedDivide(value, divisor) {
    return order(divisor[1], zero[0]) < 0 ? divide(negative(value), negative(divisor)) : divide(value, divisor);
}

function evaluate(coefficients, x) {
    return coefficients.reduceRight((value, coefficient) => add(coefficient, multiply(x, value)), zero);
}

function integrate(coefficients) {
    return [zero, ...coefficients.map((coefficient, power) => divide(coefficient, exact(power + 1)))];
}

function power(x, degree) {
    let product = one;
    for (let step = 0; step < degree; step++) product = multiply(product, x);
    return product;
}

/** Solve the six free degrees of freedom using exact elimination. The
 * fixed-base frame stiffness is positive definite, so each pivot is positive.
 */
function solve(stiffness, load) {
    const rows = stiffness.map((row, index) => [...row, load[index]]);
    for (let pivot = 0; pivot < rows.length; pivot++) {
        const divisor = rows[pivot][pivot];
        rows[pivot] = rows[pivot].map(value => divide(value, divisor));
        for (let index = 0; index < rows.length; index++) {
            if (index === pivot) continue;
            const factor = rows[index][pivot];
            rows[index] = rows[index].map((value, column) => subtract(value, multiply(factor, rows[pivot][column])));
        }
    }
    return rows.map(row => row.at(-1));
}

/** Assemble the two columns and beam in the order uB,vB,thetaB,uC,vC,thetaC.
 * For the vertical columns local transverse displacement equals minus u.
 */
function portalStiffness() {
    const beamAxial = divide(EA, L);
    const columnAxial = divide(EA, H);
    const beamBending = divide(multiply(exact(12), EI), power(L, 3));
    const columnBending = divide(multiply(exact(12), EI), power(H, 3));
    const beamCoupling = divide(multiply(exact(6), EI), power(L, 2));
    const columnCoupling = divide(multiply(exact(6), EI), power(H, 2));
    const beamRotation = divide(multiply(exact(4), EI), L);
    const columnRotation = divide(multiply(exact(4), EI), H);
    const beamCrossRotation = divide(beamRotation, exact(2));
    const axial = add(beamAxial, columnBending);
    const vertical = add(columnAxial, beamBending);
    const rotational = add(columnRotation, beamRotation);
    const minusAxial = negative(beamAxial), minusBending = negative(beamBending), minusCoupling = negative(beamCoupling);
    return [
        [axial, zero, columnCoupling, minusAxial, zero, zero],
        [zero, vertical, beamCoupling, zero, minusBending, beamCoupling],
        [columnCoupling, beamCoupling, rotational, zero, minusCoupling, beamCrossRotation],
        [minusAxial, zero, zero, axial, zero, columnCoupling],
        [zero, minusBending, minusCoupling, zero, vertical, minusCoupling],
        [zero, beamCoupling, beamCrossRotation, columnCoupling, minusCoupling, rotational],
    ];
}

/** Integrate the distributed load against the four cubic Hermite functions
 * of r=x/L, each scaled to its translation or rotation degree of freedom.
 */
function equivalentLoad(start, end, startIntensity, gradient) {
    const a = divide(start, L), b = divide(end, L);
    const shapes = [[1, 0, -3, 2], [0, 6, -12, 6], [0, 0, 3, -2], [0, 0, -6, 6]];
    const intercept = subtract(startIntensity, multiply(gradient, start));
    const rGradient = multiply(gradient, L);
    return shapes.map(shape => {
        const values = shape.map(exact);
        const product = [...values, zero].map((value, index) => add(multiply(value, intercept),
            multiply(values[index - 1] ?? zero, rGradient)));
        const integral = integrate(product);
        return multiply(negative(L), subtract(evaluate(integral, b), evaluate(integral, a)));
    });
}

function beamStartActions(free, load) {
    const [ , vB, thetaB, , vC, thetaC] = free;
    const shift = subtract(vB, vC);
    const rotationSum = add(thetaB, thetaC);
    const stiffnessShear = add(multiply(divide(multiply(exact(12), EI), power(L, 3)), shift),
        multiply(divide(multiply(exact(6), EI), power(L, 2)), rotationSum));
    const stiffnessMoment = add(multiply(divide(multiply(exact(6), EI), power(L, 2)), shift),
        multiply(divide(multiply(exact(2), EI), L), add(multiply(exact(2), thetaB), thetaC)));
    return [subtract(stiffnessShear, load[0]), subtract(load[1], stiffnessMoment)];
}

function shearZeros([startShear, minusIntensity, minusHalfGradient]) {
    if (order(minusHalfGradient[0], zero[0]) === 0) {
        return order(minusIntensity[0], zero[0]) === 0 ? [] : [signedDivide(negative(startShear), minusIntensity)];
    }
    const discriminant = subtract(power(minusIntensity, 2), multiply(exact(4), multiply(minusHalfGradient, startShear)));
    if (order(discriminant[1], zero[0]) < 0) return [];
    const offset = sqrt(discriminant);
    const denominator = multiply(exact(2), minusHalfGradient);
    const centre = negative(minusIntensity);
    if (order(discriminant[1], zero[0]) === 0) return [signedDivide(centre, denominator)];
    return [signedDivide(add(centre, offset), denominator), signedDivide(subtract(centre, offset), denominator)];
}

/** Recover BC actions from exact free-joint equilibrium. Each output piece
 * uses x minus the piece start, with both end faces and strict stationary
 * points reported as moment candidates.
 */
export function portalExerciseReference({ start = zero, end = L, wStart = exact(6), wEnd = exact(-6) } = {}) {
    if (order(start[0], zero[0]) < 0 || order(end[1], L[1]) > 0 || order(start[1], end[0]) >= 0) {
        throw new RangeError('The load interval must have positive length within BC');
    }
    const gradient = divide(subtract(wEnd, wStart), subtract(end, start));
    const equivalent = equivalentLoad(start, end, wStart, gradient);
    const [forceB, coupleB, forceC, coupleC] = equivalent;
    const free = solve(portalStiffness(), [zero, forceB, coupleB, zero, forceC, coupleC]);
    let [nextShear, nextMoment] = beamStartActions(free, equivalent);
    const pieces = [], candidates = [];
    for (const [from, to, intensity, rate] of [[zero, start, zero, zero], [start, end, wStart, gradient], [end, L, zero, zero]]) {
        const length = subtract(to, from);
        if (order(length[0], zero[0]) === 0) continue;
        const shear = [nextShear, negative(intensity), divide(negative(rate), exact(2))];
        const moment = integrate(shear);
        moment[0] = nextMoment;
        const index = pieces.length;
        pieces.push({ start: bounds(from), end: bounds(to), shear: shear.map(bounds), moment: moment.map(bounds) });
        const roots = shearZeros(shear).filter(x => order(x[0], zero[0]) > 0 && order(x[1], length[1]) < 0)
            .sort((a, b) => order(a[0], b[0]));
        const addCandidate = (side, x) => candidates.push({
            piece: index, side, x: bounds(add(from, x)), m: bounds(evaluate(moment, x)),
        });
        addCandidate('start', zero);
        for (const root of roots) addCandidate('stationary', root);
        addCandidate('end', length);
        nextShear = evaluate(shear, length);
        nextMoment = evaluate(moment, length);
    }
    const antisymmetricLoad = order(add(start, end)[0], L[0]) === 0 && order(add(wStart, wEnd)[0], zero[0]) === 0;
    return { antisymmetricLoad, pieces, candidates };
}
