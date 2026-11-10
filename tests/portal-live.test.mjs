import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
import { example } from '../web/engine.ts';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js')) return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { portalAmplitude, portalCandidate, encodeCandidate, roundedDecimal } = await import('../web/portal-candidate.ts');

test('complete structural profile admits only equal signed uniform amplitudes and labels', () => {
    for (const value of [-5, -12, 0, 5, 0.1, Number.MIN_VALUE]) {
        const model = example('frame');
        model.loads[0].fy = model.loads[0].qEnd = value;
        model.loads[0].label = 'w';
        assert.equal(portalAmplitude(model), value);
    }
    const edits = [
        m => m.loads[0].fy--, m => m.loads[0].t = 0.1, m => m.loads[0].member = 'AB',
        m => m.loads.push({ ...m.loads[0], id: 'extra' }), m => m.nodes[0].x = 1,
        m => m.members[0].EI++, m => m.supports[0].kind = 'pin',
        m => m.members.reverse(), m => m.nodes[1].referenceMember = 'BC',
        m => m.members[0].connectionB = { axial: 'rigid', transverse: 'rigid', rotation: 'free' },
        m => m.loads[0].fx = 1, m => m.supports[0].angle = 0,
    ];
    for (const edit of edits) { const model = example('frame'); edit(model); assert.throws(() => portalAmplitude(model)); }
});

test('exact binary64 candidate packets and explicit bounds', () => {
    const values = portalCandidate(0.1);
    assert.deepEqual(values[0], { numerator: '3602879701896397', denominator: '36028797018963968' });
    assert.equal(new TextDecoder().decode(encodeCandidate(values)).split('\n').length, 42);
    for (const value of [Number.MIN_VALUE, Number.MAX_VALUE]) assert.throws(() => encodeCandidate(portalCandidate(value)), /Limit exceeded/);
    assert.throws(() => portalCandidate(Infinity));
    assert.deepEqual(portalCandidate(-0), portalCandidate(0));
    assert.throws(() => encodeCandidate(values.slice(1)), /dimension/);
    assert.throws(() => encodeCandidate(values.map((x, i) => i ? x : { numerator: '01', denominator: '1' })), /Malformed/);
});

test('display rounding retains signs, units and tiny exact nonzero values', () => {
    const baseline = portalCandidate(-5);
    assert.equal(roundedDecimal(baseline[19], 3), '11.262');
    assert.equal(roundedDecimal(baseline[20], 3, 1000n), '-1.720');
    assert.equal(roundedDecimal({ numerator: '-1', denominator: '2000' }, 3), '-0.001');
    assert.equal(roundedDecimal({ numerator: '-1', denominator: '1000000' }, 3), '0.000');
});
