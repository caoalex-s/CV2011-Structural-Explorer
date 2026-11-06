import test from 'node:test';
import assert from 'node:assert/strict';
import { emitExactExpression } from '../scripts/exact-geometry-expressions.mjs';

const one = { numerator: '1', denominator: '1' };
test('synthetic expression emitter enforces its closed grammar', () => {
    assert.equal(emitExactExpression({ op: 'square', args: [one] }), '(((1 : ℝ) / 1))^2');
    for (const invalid of [
        { numerator: '1', denominator: '0' }, { numerator: '1); #eval 3', denominator: '1' },
        { numerator: '01', denominator: '1' }, { numerator: '-0', denominator: '1' }, { op: 'shell', args: [] },
        { op: 'sqrt', args: [one, one] }, { op: 'pi', args: [one] },
        { op: 'add', args: [one] }, { op: 'divide', args: [one, { numerator: '0', denominator: '1' }] }, { op: '__proto__', args: [] },
    ]) assert.throws(() => emitExactExpression(invalid));
});
