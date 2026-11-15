import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { proposeInclinedPacket } = await import('../web/frame-interval-packet.ts');
const { frameQueryConvention } = await import('../web/frame-candidate.ts');
const { fraction, compare, mul } = await import('../web/frame-rational.ts');

const source = {
    nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 1, y: 2 }],
    members: [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }],
    supports: [{ id: 'S', member: 'AB', kind: 'fixed', t: 0, angle: 90 }],
    loads: [{ id: 'P', member: 'AB', kind: 'force', t: 1, end: 1, fx: 3, fy: -7, mz: 0, qEnd: 0 }],
};
const query = { member: 'AB', parameter: 1, cutSide: 'left', ...frameQueryConvention };

test('compact packet preserves source/query and includes only the bounded numerical proposal', () => {
    const result = proposeInclinedPacket(source, query, 96);
    assert.deepEqual(Object.keys(result).sort(), ['coordinates', 'packet', 'precisionBits']);
    assert.equal(result.coordinates, 3);
    const tokens = new TextDecoder().decode(result.packet).split('\n');
    let cursor = 0;
    const next = () => tokens[cursor++];
    const rational = () => fraction(BigInt(next()), BigInt(next()));
    const expectRational = value => assert.deepEqual(rational(), fraction(BigInt(value)));
    assert.equal(next(), 'CV2011_INCLINED_1');
    assert.deepEqual([next(), next(), next(), next()], ['2', '1', '1', '1']);
    for (const [id, x, y] of [['0041', 0, 0], ['0042', 1, 2]]) {
        assert.equal(next(), id);
        expectRational(x); expectRational(y);
        assert.equal(next(), '0'); assert.equal(next(), '0'); expectRational(0);
    }
    assert.equal(next(), '00410042');
    assert.equal(next(), '0'); assert.equal(next(), '1');
    expectRational(2000000); expectRational(20000); assert.equal(next(), '1');
    assert.equal(next(), '0053'); assert.equal(next(), '0'); expectRational(0);
    assert.equal(next(), '1'); expectRational(90);
    assert.equal(next(), '0050'); assert.equal(next(), '0'); assert.equal(next(), '0');
    for (const value of [1, 1, 3, -7, 0, 0]) expectRational(value);
    assert.equal(next(), '0'); expectRational(1);
    assert.equal(next(), '0'); assert.equal(next(), '1'); assert.equal(next(), '96');
    const lower = rational(), upper = rational();
    assert.ok(compare(mul(lower, lower), fraction(5n)) <= 0);
    assert.ok(compare(mul(upper, upper), fraction(5n)) >= 0);
    for (let entry = 0; entry < 3 * 3 + 3; entry++) rational();
    assert.equal(cursor, tokens.length, 'No intermediate matrices or claimed output values may follow.');
    assert.ok(tokens.length <= 6000 && result.packet.length <= 1048576);
});

test('precision and source/query mutations are rejected or preserved in distinct packets', () => {
    assert.throws(() => proposeInclinedPacket(source, query, 80), /precision/);
    assert.throws(() => proposeInclinedPacket(source, { ...query, cutSide: 'right' }, 96), /endpoint/);
    const changed = structuredClone(source);
    changed.loads[0].fx = 4;
    assert.notDeepEqual(proposeInclinedPacket(changed, query, 96).packet,
        proposeInclinedPacket(source, query, 96).packet);
    const oversized = structuredClone(source);
    oversized.loads[0].id = 'x'.repeat(257);
    assert.throws(() => proposeInclinedPacket(oversized, query, 96), /256/);
});
