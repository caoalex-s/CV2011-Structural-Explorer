import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { decodeAcceptedIntervalReport } = await import('../web/frame-interval-result.ts');
const bytes = tokens => new TextEncoder().encode(tokens.join('\n'));
const zero = ['0', '1', '0', '1', '0', '1'];
function representationFixture() {
    // This is a representation fixture, not evidence of a physical solution.
    return ['CV2011_INCLINED_RESULT_1', '00410042', '1', '2', '0', '1', '1',
        ...Array.from({ length: 6 }, () => ['-1', '2', '3', '2', '1', '2']).flat(),
        '0', '0', '0041d83dde00', '0', '1', ...zero, ...zero, ...zero];
}

test('report representation retains exact endpoints, midpoint and source identities', () => {
    const result = decodeAcceptedIntervalReport(bytes(representationFixture()));
    assert.deepEqual(result.query, { member: 'AB', parameter: { numerator: '1', denominator: '2' },
        cutSide: 'left', convention: 1 });
    assert.equal(result.points[0].id, 'A😀');
    assert.equal(result.points[0].owner, 'node');
    assert.deepEqual(result.fields[0], {
        lower: { numerator: '-1', denominator: '2' }, upper: { numerator: '3', denominator: '2' },
        midpoint: { numerator: '1', denominator: '2' },
    });
    assert.equal('state' in result, false, 'Parsing cannot grant checker status.');
});

test('high precision readouts are preserved as rationals without binary64 conversion', () => {
    const tokens = representationFixture();
    tokens.splice(7, 6, '1', String(1n << 128n), '3', String(1n << 128n), '1', String(1n << 127n));
    const result = decodeAcceptedIntervalReport(bytes(tokens));
    assert.equal(result.fields[0].lower.denominator, String(1n << 128n));
    assert.equal(result.fields[0].midpoint.denominator, String(1n << 127n));
});

test('report corruption and preallocation limits fail closed', () => {
    const wrongMidpoint = representationFixture();
    wrongMidpoint[11] = '3';
    assert.throws(() => decodeAcceptedIntervalReport(bytes(wrongMidpoint)), /midpoint/);
    const reversed = representationFixture();
    reversed.splice(7, 4, '2', '1', '1', '1');
    assert.throws(() => decodeAcceptedIntervalReport(bytes(reversed)), /Reversed/);
    const oversizedCount = representationFixture();
    oversizedCount[6] = '17';
    assert.throws(() => decodeAcceptedIntervalReport(bytes(oversizedCount)), /count/);
    const longNumerator = representationFixture();
    longNumerator[7] = '1'.repeat(130);
    assert.throws(() => decodeAcceptedIntervalReport(bytes(longNumerator)), /rational/);
    assert.throws(() => decodeAcceptedIntervalReport(bytes([...representationFixture(), '0'])), /trailing/);
    assert.throws(() => decodeAcceptedIntervalReport(new Uint8Array(262145)), /byte budget/);
    assert.throws(() => decodeAcceptedIntervalReport(bytes(Array(1025).fill('0'))), /Too many/);
});
