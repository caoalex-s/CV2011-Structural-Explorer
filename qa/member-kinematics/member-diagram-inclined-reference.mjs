/** Independent inclined cantilever references for h=2 m or h=3 m.
 * The fixed end is A=(0,0) and the free end is B=(4,h). All intervals have exact
 * rational endpoints. Roots are bracketed at about 240 binary digits to
 * validate even very narrow checker enclosures.
 */

const scale = 2n ** 240n;

function gcd(a, b) {
    while (b !== 0n) [a, b] = [b, a % b];
    return a < 0n ? -a : a;
}

function rational(top, bottom = 1n) {
    const common = gcd(top, bottom);
    const sign = bottom < 0n ? -1n : 1n;
    return [sign * top / common, sign * bottom / common];
}

function compare(a, b) {
    const difference = a[0] * b[1] - b[0] * a[1];
    return difference < 0n ? -1 : difference > 0n ? 1 : 0;
}

function addRatio(a, b) {
    return rational(a[0] * b[1] + b[0] * a[1], a[1] * b[1]);
}

function multiplyRatio(a, b) {
    return rational(a[0] * b[0], a[1] * b[1]);
}

function exact(value) {
    const point = rational(BigInt(value));
    return [point, point];
}

function add(a, b) {
    return [addRatio(a[0], b[0]), addRatio(a[1], b[1])];
}

function negative(a) {
    return [[-a[1][0], a[1][1]], [-a[0][0], a[0][1]]];
}

function subtract(a, b) {
    return add(a, negative(b));
}

function multiply(a, b) {
    const corners = a.flatMap(x => b.map(y => multiplyRatio(x, y))).sort(compare);
    return [corners[0], corners.at(-1)];
}

function divide(a, b) {
    if (compare(b[0], [0n, 1n]) <= 0) throw Error('Expected a positive divisor interval');
    return multiply(a, [rational(b[1][1], b[1][0]), rational(b[0][1], b[0][0])]);
}

/** Floor of the nonnegative square root by monotone integer Newton iteration. */
function integerRoot(n) {
    if (n < 2n) return n;
    let guess = 1n << BigInt(Math.ceil(n.toString(2).length / 2));
    while (true) {
        const next = (guess + n / guess) / 2n;
        if (next >= guess) return guess;
        guess = next;
    }
}

function rootBounds([top, bottom]) {
    if (top < 0n) throw Error('Expected a nonnegative radicand');
    const rootTop = integerRoot(top), rootBottom = integerRoot(bottom);
    if (rootTop ** 2n === top && rootBottom ** 2n === bottom) {
        const root = rational(rootTop, rootBottom);
        return [root, root];
    }
    // Flooring the scaled radicand leaves the floor of its root unchanged.
    const low = integerRoot(top * scale ** 2n / bottom);
    return [rational(low, scale), rational(low + 1n, scale)];
}

function sqrt(interval) {
    return [rootBounds(interval[0])[0], rootBounds(interval[1])[1]];
}

function ratioText([top, bottom]) {
    return `${top}/${bottom}`;
}

function bounds(interval) {
    return interval.map(ratioText);
}

/** Check that a reported rational interval contains this independent
 * enclosure. A reference can be narrower than the displayed precision.
 */
export function enclosesReference(reported, reference) {
    const parse = text => {
        if (!/^-?\d+\/[1-9]\d*$/.test(text)) throw Error('Expected a rational numerator and positive denominator');
        return text.split('/').map(BigInt);
    };
    return compare(parse(reported[0]), parse(reference[0])) <= 0 &&
        compare(parse(reference[1]), parse(reported[1])) <= 0;
}

/** Downward tip force 5 kN and full-span downward-positive w=6−12t kN/m.
 * The local x direction starts at the first drawn end. Reverse drawing
 * keeps the shear and changes the signs and sides of the moment field.
 */
export function affineInclinedCantilever(height, reversed = false, loadScale = 1) {
    if (height !== 2 && height !== 3) throw Error('Use a rise of 2 m or 3 m');
    if (loadScale !== 1 && loadScale !== 2) throw Error('Use the initial or doubled load');
    const lengthSquared = exact(16 + height ** 2);
    const length = sqrt(lengthSquared);
    const perUnitShear = divide(exact(20), length);
    const startShear = multiply(exact(loadScale), perUnitShear);
    const midDistance = divide(length, exact(2));
    const startMoment = reversed ? exact(0) : subtract(multiply(exact(4 * loadScale), length), exact(20 * loadScale));
    const endMoment = reversed ? subtract(exact(20 * loadScale), multiply(exact(4 * loadScale), length)) : exact(0);
    const midMoment = divide(add(startMoment, endMoment), exact(2));
    const midParameter = divide(exact(1), exact(2));
    const offset = sqrt(divide(subtract(exact(6), perUnitShear), exact(24)));
    const physicalOffset = multiply(length, offset);
    const momentAmplitude = multiply(multiply(exact(16 * loadScale), length), multiply(multiply(offset, offset), offset));
    const row = (field, side, parameter, position, value, min = false, max = false) =>
        ({ field, side, index: 0, t: bounds(parameter), x: bounds(position), value: bounds(value), min, max });
    return {
        length: bounds(length),
        piece: {
            a: '0/1', b: '1/1', length: bounds(length),
            start: bounds(exact(0)), end: bounds(length),
            shear: [startShear, divide(exact(-24 * loadScale), length), divide(exact(24 * loadScale), lengthSquared), exact(0)].map(bounds),
            moment: [startMoment, startShear, divide(exact(-12 * loadScale), length), divide(exact(8 * loadScale), lengthSquared)].map(bounds),
            normalizedShear: [startShear, exact(-24 * loadScale), exact(24 * loadScale), exact(0)].map(bounds),
            normalizedMoment: [startMoment, exact(20 * loadScale), multiply(exact(-12 * loadScale), length),
                multiply(exact(8 * loadScale), length)].map(bounds),
        },
        candidates: [
            row('V', 'start', exact(0), exact(0), startShear, false, true),
            row('V', 'interior', midParameter, midDistance, subtract(startShear, exact(6 * loadScale)), true),
            row('V', 'end', exact(1), length, startShear, false, true),
            row('M', 'start', exact(0), exact(0), startMoment),
            row('M', 'interior', subtract(midParameter, offset), subtract(midDistance, physicalOffset),
                add(midMoment, momentAmplitude), false, true),
            row('M', 'interior', add(midParameter, offset), add(midDistance, physicalOffset),
                subtract(midMoment, momentAmplitude), true),
            row('M', 'end', exact(1), length, endMoment),
        ],
    };
}

/** A=(0,0) fixed, B=(4,2) free. A 10 kN downward force at t=1/2 gives
 * a shear jump and a 6 kN m CCW couple at t=3/4 gives a moment jump.
 * Each piece uses its own local fraction r from zero to one.
 */
export function inclinedJumpCantilever() {
    const length = sqrt(exact(20));
    const shearBeforeForce = divide(exact(40), length);
    const zero = exact(0);
    const pieceCoefficients = [
        { shear: [shearBeforeForce, zero, zero, zero],
            moment: [exact(-14), exact(20), zero, zero] },
        { shear: [zero, zero, zero, zero], moment: [exact(6), zero, zero, zero] },
        { shear: [zero, zero, zero, zero], moment: [zero, zero, zero, zero] },
    ];
    const parameters = [zero, divide(exact(1), exact(2)), divide(exact(3), exact(4)), exact(1)];
    const pieces = pieceCoefficients.map(({shear, moment}, index) => ({
        a: ratioText(parameters[index][0]), b: ratioText(parameters[index + 1][0]),
        length: bounds(multiply(length, subtract(parameters[index + 1], parameters[index]))),
        start: bounds(multiply(length, parameters[index])),
        end: bounds(multiply(length, parameters[index + 1])),
        normalizedShear: shear.map(bounds), normalizedMoment: moment.map(bounds),
    }));
    const candidates = [];
    const row = (index, field, side, value, min, max) => {
        const first = parameters[index], last = parameters[index + 1];
        const t = side === 'flat' ? [first[0], last[1]] : side === 'start' ? first : last;
        return { index, field, side, t: bounds(t), x: bounds(multiply(length, t)), value: bounds(value), min, max };
    };
    for (const [index, {shear, moment}] of pieceCoefficients.entries()) {
        for (const side of ['start', 'flat', 'end']) {
            candidates.push(row(index, 'V', side, shear[0], index !== 0, index === 0));
        }
        if (index === 0) {
            candidates.push(row(index, 'M', 'start', moment[0], true, false));
            candidates.push(row(index, 'M', 'end', exact(6), false, true));
        } else {
            for (const side of ['start', 'flat', 'end']) {
                candidates.push(row(index, 'M', side, moment[0], false, index === 1));
            }
        }
    }
    return { length: bounds(length), pieces, candidates };
}

/** Select B–C after drawing fixed A, released B and pinned C. A 10 kN
 * downward force at the midpoint gives both unloaded end moments zero.
 * The local shear follows from transverse balance at the two zero-moment ends.
 */
export function inclinedHingeSpan() {
    const length = sqrt(exact(20));
    const half = divide(exact(1), exact(2));
    const zero = exact(0), ten = exact(10);
    const positiveShear = divide(exact(20), length);
    const cuts = [zero, half, exact(1)];
    const pieces = [], candidates = [];
    for (const [index, shear] of [positiveShear, negative(positiveShear)].entries()) {
        const first = cuts[index], last = cuts[index + 1];
        const firstMoment = index === 0 ? zero : ten;
        const lastMoment = index === 0 ? ten : zero;
        pieces.push({
            a: ratioText(first[0]), b: ratioText(last[0]), length: bounds(multiply(length, half)),
            start: bounds(multiply(length, first)), end: bounds(multiply(length, last)),
            normalizedShear: [shear, zero, zero, zero].map(bounds),
            normalizedMoment: [firstMoment, subtract(lastMoment, firstMoment), zero, zero].map(bounds),
        });
        const row = (field, side, t, value, min, max) =>
            ({ field, side, index, t: bounds(t), x: bounds(multiply(length, t)), value: bounds(value), min, max });
        candidates.push(
            row('V', 'start', first, shear, index === 1, index === 0),
            row('V', 'flat', [first[0], last[1]], shear, index === 1, index === 0),
            row('V', 'end', last, shear, index === 1, index === 0),
            row('M', 'start', first, firstMoment, index === 0, index === 1),
            row('M', 'end', last, lastMoment, index === 1, index === 0),
        );
    }
    return { length: bounds(length), pieces, candidates };
}

/** Select inclined BC of a two-member cantilever, with a spring of 5000
 * kN m/rad at B, tip force 5 kN down and tip couple 30 kN m CCW at C.
 */
export function inclinedSpringSpan(reversed = false) {
    const length = sqrt(exact(20));
    const zero = exact(0), one = exact(1);
    const shear = divide(exact(20), length);
    const startMoment = exact(reversed ? -30 : 10);
    const endMoment = exact(reversed ? -10 : 30);
    const row = (field, side, t, value, min, max) =>
        ({ field, side, index: 0, t: bounds(t), x: bounds(multiply(length, t)), value: bounds(value), min, max });
    return {
        length: bounds(length),
        springMoment: bounds(exact(10)),
        relativeRotation: bounds(divide(one, exact(500))),
        pieces: [{
            a: '0/1', b: '1/1', length: bounds(length),
            start: bounds(zero), end: bounds(length),
            normalizedShear: [shear, zero, zero, zero].map(bounds),
            normalizedMoment: [startMoment, exact(20), zero, zero].map(bounds),
        }],
        candidates: [
            row('V', 'start', zero, shear, true, true),
            row('V', 'flat', [zero[0], one[1]], shear, true, true),
            row('V', 'end', one, shear, true, true),
            row('M', 'start', zero, startMoment, true, false),
            row('M', 'end', one, endMoment, false, true),
        ],
    };
}

// The deformation benchmarks use the same independent rational arithmetic.
export { exact, add, subtract, multiply, divide, negative, sqrt, bounds };
