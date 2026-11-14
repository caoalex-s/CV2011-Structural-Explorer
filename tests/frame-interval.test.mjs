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
