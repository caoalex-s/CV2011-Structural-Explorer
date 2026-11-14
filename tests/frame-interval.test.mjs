import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { IntervalArithmetic } = await import('../web/frame-interval.ts');
const { degreeAxes, degreeClass, memberGeometry } = await import('../web/frame-interval-geometry.ts');
const { pointBasis } = await import('../web/frame-interval-basis.ts');
const { enclosureAccuracy } = await import('../web/frame-interval-accuracy.ts');
const { proposeIntervalSolution, intervalDot } = await import('../web/frame-interval-solve.ts');
const { compileIntervalFrame } = await import('../web/frame-interval-model.ts');
const { recoverIntervalFields } = await import('../web/frame-interval-fields.ts');
const { frameQueryConvention } = await import('../web/frame-candidate.ts');
const { fraction, compare, add, sub, mul, div } = await import('../web/frame-rational.ts');
const contains = (interval, value) => {
    assert.ok(compare(interval.lower, value) <= 0);
    assert.ok(compare(value, interval.upper) <= 0);
};

test('outward operations contain exact rational results across all sign combinations', () => {
    const arithmetic = new IntervalArithmetic(32);
    for (let a = -7n; a <= 7n; a++) for (let b = -7n; b <= 7n; b++) {
        const x = fraction(a, 3n), y = fraction(b, 5n);
        const ix = arithmetic.bounds(x), iy = arithmetic.bounds(y);
        contains(ix, x); contains(iy, y);
        contains(arithmetic.add(ix, iy), add(x, y));
        contains(arithmetic.subtract(ix, iy), sub(x, y));
        contains(arithmetic.multiply(ix, iy), mul(x, y));
        if (b !== 0n) contains(arithmetic.divide(ix, iy), div(x, y));
    }
});

test('square-root bounds satisfy exact squared inequalities and refine irrational lengths', () => {
    let previous;
    for (const bits of [32, 64, 96, 128]) {
        const arithmetic = new IntervalArithmetic(bits), five = fraction(5n);
        const bounds = arithmetic.squareRoot(arithmetic.bounds(five));
        assert.ok(compare(mul(bounds.lower, bounds.lower), five) < 0);
        assert.ok(compare(mul(bounds.upper, bounds.upper), five) > 0);
        if (previous) {
            assert.ok(compare(previous.lower, bounds.lower) <= 0);
            assert.ok(compare(bounds.upper, previous.upper) <= 0);
        }
        previous = bounds;
        assert.deepEqual(arithmetic.squareRoot(arithmetic.bounds(fraction(9n))), arithmetic.bounds(fraction(3n)));
    }
});

test('zero-crossing division, invalid domains and exhausted budgets cannot return an enclosure', () => {
    const arithmetic = new IntervalArithmetic(32);
    assert.throws(() => arithmetic.divide(arithmetic.bounds(fraction(1n)), arithmetic.bounds(fraction(-1n), fraction(1n))), /Inconclusive/);
    assert.throws(() => arithmetic.squareRoot(arithmetic.bounds(fraction(-1n))), /Inconclusive/);
    assert.throws(() => arithmetic.bounds(fraction(2n), fraction(1n)), /reversed/);
    const limited = new IntervalArithmetic(32, 1);
    limited.bounds(fraction(0n));
    assert.throws(() => limited.bounds(fraction(1n)), /budget exhausted/);
});

test('degree aliases are exact and 45-degree enclosures satisfy independent squared identities', () => {
    assert.deepEqual(degreeClass(fraction(-143n), 180), fraction(37n));
    assert.deepEqual(degreeClass(fraction(397n), 360), fraction(37n));
    const arithmetic = new IntervalArithmetic(128);
    assert.deepEqual(degreeAxes(arithmetic, fraction(450n)), {
        cosine: arithmetic.bounds(fraction(0n)), sine: arithmetic.bounds(fraction(1n)),
    });
    const diagonal = degreeAxes(arithmetic, fraction(45n));
    for (const component of [diagonal.cosine, diagonal.sine]) {
        assert.ok(compare(component.lower, fraction(0n)) > 0);
        assert.ok(compare(mul(component.lower, component.lower), fraction(1n, 2n)) < 0);
        assert.ok(compare(mul(component.upper, component.upper), fraction(1n, 2n)) > 0);
        assert.ok(compare(sub(component.upper, component.lower), fraction(1n, 10n ** 16n)) < 0);
    }
    assert.deepEqual(degreeAxes(arithmetic, fraction(-323n)), degreeAxes(arithmetic, fraction(37n)));
});

test('member geometry keeps irrational length and reversed direction in its enclosure', () => {
    const arithmetic = new IntervalArithmetic(96);
    const forward = memberGeometry(arithmetic, fraction(1n), fraction(2n));
    const reversed = memberGeometry(arithmetic, fraction(-1n), fraction(-2n));
    assert.deepEqual(forward.length, reversed.length);
    assert.deepEqual(arithmetic.negate(forward.cosine), reversed.cosine);
    assert.deepEqual(arithmetic.negate(forward.sine), reversed.sine);
    assert.throws(() => memberGeometry(arithmetic, fraction(0n), fraction(0n)), /coincident/);
});

test('basis preserves all duplicate sources and distinguishes exact near-parallel classes', () => {
    const arithmetic = new IntervalArithmetic(96);
    const roller = angle => ({ id: String(angle), member: 'AB', t: 0, kind: 'roller', angle });
    const repeated = pointBasis(arithmetic, [roller(37), roller(217), roller(-143)]);
    assert.equal(repeated.sourceSupportCount, 3);
    assert.deepEqual(repeated.classes[0].sourceIndices, [0, 1, 2]);
    assert.deepEqual(repeated.columns.map(column => column.coordinate), ['tangent', 'rotation']);
    const distinct = pointBasis(arithmetic, [roller(37), roller(37 + 2 ** -40)]);
    assert.equal(distinct.classes.length, 2);
    assert.deepEqual(distinct.columns.map(column => column.coordinate), ['rotation']);
    assert.deepEqual(pointBasis(arithmetic, [{ ...roller(37), kind: 'fixed' }, roller(217)]).columns, []);
    assert.deepEqual(pointBasis(arithmetic, []).columns.map(column => column.coordinate), ['x', 'y', 'rotation']);
});

test('accuracy uses exact absolute thresholds near zero and bounds a separate estimate independently', () => {
    const lower = fraction(-1n, 1000000n), upper = fraction(1n, 1000000n);
    const force = enclosureAccuracy('N', { lower, upper }, fraction(1n));
    assert.equal(force.meetsTarget, true);
    assert.deepEqual(force.relativeTolerance, fraction(1n, 100000000n));
    assert.deepEqual(force.estimateError, fraction(1000001n, 1000000n));
    assert.equal(enclosureAccuracy('ux', { lower, upper }).meetsTarget, false);
    const tooWide = enclosureAccuracy('N', { lower: fraction(-1000001n, 10n ** 12n), upper });
    assert.equal(tooWide.meetsTarget, false);
    assert.throws(() => enclosureAccuracy('M', { lower: upper, upper: lower }), /reversed/);
});

test('inverse residual encloses independent rational solutions and uncertain coefficients', () => {
    const arithmetic = new IntervalArithmetic(96);
    const point = n => arithmetic.bounds(fraction(BigInt(n)));
    const result = proposeIntervalSolution(arithmetic, [[point(2), point(1)], [point(1), point(2)]], [point(1), point(0)]);
    contains(result.enclosure[0], fraction(2n, 3n));
    contains(result.enclosure[1], fraction(-1n, 3n));
    assert.ok(compare(result.contraction, fraction(1n)) < 0);
    const uncertain = proposeIntervalSolution(arithmetic, [[arithmetic.bounds(fraction(2n), fraction(3n))]], [point(1)]);
    contains(uncertain.enclosure[0], fraction(1n, 3n));
    contains(uncertain.enclosure[0], fraction(1n, 2n));
    assert.throws(() => proposeIntervalSolution(arithmetic, [[point(1), point(1)], [point(1), point(1)]], [point(1), point(0)]), /Inconclusive/);
    assert.deepEqual(proposeIntervalSolution(arithmetic, [], []).enclosure, []);
});

test('source assembly encloses irrational cantilever closed forms without normalizing rounded cosines', () => {
    const source = {
        nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 1, y: 2 }],
        members: [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }],
        supports: [{ id: 'S', member: 'AB', kind: 'fixed', t: 0, angle: 90 }],
        loads: [{ id: 'P', member: 'AB', kind: 'force', t: 1, end: 1, fx: 3, fy: -7, mz: 0, qEnd: 0 }],
    };
    const arithmetic = new IntervalArithmetic(96);
    const frame = compileIntervalFrame(arithmetic, source, { member: 'AB', parameter: 1, cutSide: 'left', ...frameQueryConvention });
    const proposed = proposeIntervalSolution(arithmetic, frame.reduced, frame.reducedForce);
    const motion = frame.basis.map(row => intervalDot(arithmetic, row, proposed.enclosure));
    const reaction = frame.stiffness.map((row, i) => arithmetic.subtract(intervalDot(arithmetic, row, motion), frame.force[i]));
    for (let i = 0; i < 3; i++) contains(reaction[i], fraction(BigInt([-3,7,13][i])));
    // Independent closed forms in global axes, using a narrower sqrt bracket.
    const reference = new IntervalArithmetic(128), root = reference.squareRoot(reference.bounds(fraction(5n)));
    const axialTip = fraction(-11n, 2000000n), transverseTip = fraction(-65n, 60000n);
    const expected = [
        reference.divide(reference.bounds(sub(axialTip, mul(fraction(2n), transverseTip))), root),
        reference.divide(reference.bounds(add(mul(fraction(2n), axialTip), transverseTip)), root),
        reference.multiply(reference.bounds(fraction(-13n, 40000n)), root),
    ];
    expected.forEach((interval, i) => {
        contains(motion[3+i], interval.lower); contains(motion[3+i], interval.upper);
        assert.equal(enclosureAccuracy(['ux','uy','rotation'][i], motion[3+i]).meetsTarget, true);
    });
    const readouts = recoverIntervalFields(arithmetic, frame, motion);
    const referenceReadouts = [
        reference.divide(reference.bounds(fraction(-11n)), root),
        reference.divide(reference.bounds(fraction(13n)), root),
        reference.bounds(fraction(0n)), expected[2], expected[0], expected[1],
    ];
    referenceReadouts.forEach((interval, i) => {
        contains(readouts[i], interval.lower); contains(readouts[i], interval.upper);
        assert.equal(enclosureAccuracy(['N','V','M','rotation','ux','uy'][i], readouts[i]).meetsTarget, true);
    });
});

test('inclined zero-resultant affine loading retains its nonzero moment under reversal', () => {
    for (const reversed of [false, true]) {
        const arithmetic = new IntervalArithmetic(96);
        const source = {
            nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 1, y: 2 }],
            members: [{ id: 'AB', a: reversed ? 'B' : 'A', b: reversed ? 'A' : 'B', EA: 2000000, EI: 20000 }],
            supports: [{ id: 'S', member: 'AB', kind: 'fixed', t: reversed ? 1 : 0, angle: 90 }],
            loads: [{ id: 'w', member: 'AB', kind: 'distributed', t: 0, end: 1, fx: 0, fy: reversed ? 5 : -5, mz: 0, qEnd: reversed ? -5 : 5 }],
        };
        const frame = compileIntervalFrame(arithmetic, source, { member: 'AB', parameter: 0.5, cutSide: 'left', ...frameQueryConvention });
        const proposal = proposeIntervalSolution(arithmetic, frame.reduced, frame.reducedForce);
        const motion = frame.basis.map(row => intervalDot(arithmetic, row, proposal.enclosure));
        const reaction = frame.stiffness.map((row, i) => arithmetic.subtract(intervalDot(arithmetic, row, motion), frame.force[i]));
        contains(reaction[0], fraction(0n)); contains(reaction[1], fraction(0n));
        const reference = new IntervalArithmetic(128);
        const expectedMoment = reference.multiply(reference.bounds(fraction(-5n, 6n)), reference.squareRoot(reference.bounds(fraction(5n))));
        contains(reaction[2], expectedMoment.lower); contains(reaction[2], expectedMoment.upper);
        assert.equal(enclosureAccuracy('Mz', reaction[2]).meetsTarget, true);
    }
});

test('inclined roller solve preserves duplicate supports and the interior force jump', () => {
    const source = {
        nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 1, y: 2 }],
        members: [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }],
        supports: [
            { id: 'A-pin', member: 'AB', kind: 'pin', t: 0, angle: 90 },
            { id: 'B-roller', member: 'AB', kind: 'roller', t: 1, angle: 37 },
            { id: 'B-alias', member: 'AB', kind: 'roller', t: 1, angle: 217 },
        ],
        loads: [{ id: 'P', member: 'AB', kind: 'force', t: 0.5, end: 0.5, fx: 3, fy: -7, mz: 0, qEnd: 0 }],
    };
    const arithmetic = new IntervalArithmetic(96);
    const query = { member: 'AB', parameter: 0.5, cutSide: 'left', ...frameQueryConvention };
    const frame = compileIntervalFrame(arithmetic, source, query);
    assert.deepEqual(frame.supportPoints, [0, 1, 1]);
    assert.equal(frame.bases[1].sourceSupportCount, 2);
    assert.equal(frame.bases[1].classes.length, 1);
    assert.equal(frame.points[2].owner, 'member');
    const proposal = proposeIntervalSolution(arithmetic, frame.reduced, frame.reducedForce);
    const motion = frame.basis.map(row => intervalDot(arithmetic, row, proposal.enclosure));
    const reactions = frame.stiffness.map((row, i) => arithmetic.subtract(intervalDot(arithmetic, row, motion), frame.force[i]));

    // Independent statics, sharing the trig producer at higher precision:
    // Bx = R cos37, By = R sin37, By - 2 Bx = 13/2.
    // The separate Taylor-series test validates the 37-degree trig enclosure.
    const reference = new IntervalArithmetic(128);
    const normal = degreeAxes(reference, fraction(37n));
    const lever = reference.subtract(normal.sine, reference.multiply(reference.bounds(fraction(2n)), normal.cosine));
    const magnitude = reference.divide(reference.bounds(fraction(13n, 2n)), lever);
    const bx = reference.multiply(magnitude, normal.cosine);
    const by = reference.multiply(magnitude, normal.sine);
    const expected = [reference.subtract(reference.bounds(fraction(-3n)), bx),
        reference.subtract(reference.bounds(fraction(7n)), by), reference.bounds(fraction(0n)),
        bx, by, reference.bounds(fraction(0n))];
    expected.forEach((bounds, i) => {
        contains(reactions[i], bounds.lower);
        contains(reactions[i], bounds.upper);
        assert.equal(enclosureAccuracy(i % 3 === 2 ? 'Mz' : i % 3 === 0 ? 'Rx' : 'Ry', reactions[i]).meetsTarget, true);
    });

    const left = recoverIntervalFields(arithmetic, frame, motion);
    query.cutSide = 'right';
    assert.equal(frame.query.cutSide, 'left', 'the source query is copied rather than aliased');
    const right = recoverIntervalFields(arithmetic, { ...frame, query }, motion);
    const root = reference.squareRoot(reference.bounds(fraction(5n)));
    // N jumps by minus the local axial load; V jumps by the local transverse load.
    const jumps = [reference.divide(reference.bounds(fraction(11n)), root),
        reference.divide(reference.bounds(fraction(-13n)), root)];
    jumps.forEach((bounds, i) => {
        const jump = arithmetic.subtract(right[i], left[i]);
        contains(jump, bounds.lower);
        contains(jump, bounds.upper);
    });
    for (const i of [2, 3, 4, 5]) contains(arithmetic.subtract(right[i], left[i]), fraction(0n));
});

test('source identifier limits reject oversized IDs before interval assembly', () => {
    const source = {
        nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 1, y: 2 }],
        members: [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }],
        supports: [{ id: 'S', member: 'AB', kind: 'fixed', t: 0, angle: 90 }],
        loads: [{ id: 'P', member: 'AB', kind: 'force', t: 1, end: 1, fx: 3, fy: -7, mz: 0, qEnd: 0 }],
    };
    for (const group of ['nodes', 'members', 'supports', 'loads']) {
        const invalid = structuredClone(source);
        const oversized = 'x'.repeat(257);
        invalid[group][0].id = oversized;
        if (group === 'nodes') invalid.members[0].a = oversized;
        if (group === 'members') {
            invalid.supports[0].member = oversized;
            invalid.loads[0].member = oversized;
        }
        const query = { member: invalid.members[0].id, parameter: 1, cutSide: 'left', ...frameQueryConvention };
        // One arithmetic operation would be exhausted immediately in assembly.
        // Identifier rejection must occur before that budget is touched.
        assert.throws(() => compileIntervalFrame(new IntervalArithmetic(96, 1), invalid, query), /256 UTF-16/);
    }
});

test('37-degree trig enclosures contain an independent exact alternating-series reference', () => {
    // Independent rational arithmetic without the producer's digit cap permits
    // direct Taylor sums. No halving, double-angle recurrence or interval helper
    // is reused. The pi bracket is the same externally justified input premise.
    const rational = (n, d = 1n) => {
        let a = n < 0n ? -n : n;
        let b = d;
        while (b) [a, b] = [b, a % b];
        return { n: n / a, d: d / a };
    };
    const plus = (a, b) => rational(a.n * b.d + b.n * a.d, a.d * b.d);
    const times = (a, b) => rational(a.n * b.n, a.d * b.d);
    const negative = a => ({ n: -a.n, d: a.d });
    const piLow = rational(314159265358979323846n, 10n ** 20n);
    const piHigh = rational(314159265358979323847n, 10n ** 20n);
    const angleScale = rational(37n, 180n);
    const xLow = times(angleScale, piLow);
    const xHigh = times(angleScale, piHigh);

    // For 0 < x < 1, terms decrease. An even-index partial sum is an upper
    // bound and its next (negative) term gives a lower bound. Sine increases
    // and cosine decreases throughout this interval.
    const taylor = (x, sine) => {
        const xSquared = times(x, x);
        let term = sine ? x : rational(1n);
        let sum = term;
        for (let index = 1; index <= 24; index++) {
            const degree = 2 * index + (sine ? 1 : 0);
            term = negative(times(term, times(xSquared, rational(1n, BigInt(degree * (degree - 1))))));
            sum = plus(sum, term);
        }
        const nextDegree = 50 + (sine ? 1 : 0);
        const next = negative(times(term, times(xSquared, rational(1n, BigInt(nextDegree * (nextDegree - 1))))));
        return { lower: plus(sum, next), upper: sum };
    };
    const reference = {
        sine: { lower: taylor(xLow, true).lower, upper: taylor(xHigh, true).upper },
        cosine: { lower: taylor(xHigh, false).lower, upper: taylor(xLow, false).upper },
    };
    for (const bits of [32, 64, 96, 128]) {
        const actual = degreeAxes(new IntervalArithmetic(bits), fraction(37n));
        for (const component of ['sine', 'cosine']) {
            contains(actual[component], reference[component].lower);
            contains(actual[component], reference[component].upper);
        }
    }
});
