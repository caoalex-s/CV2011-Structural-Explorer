import assert from 'node:assert/strict';
import test from 'node:test';
import { registerHooks } from 'node:module';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { example } = await import('../web/engine.ts');
const { compileHingeFrame } = await import('../web/frame-hinge-candidate.ts');
const { FrameCandidates, frameQueryConvention } = await import('../web/frame-candidate.ts');
const { equal, integer, zero } = await import('../web/frame-rational.ts');
const at = (member, parameter) => ({ ...frameQueryConvention, member, parameter,
    cutSide: parameter === 0 ? 'right' : 'left' });
const solve = (model, member, t) => new FrameCandidates().produce(compileHingeFrame(model, at(member, t)));

test('two-span hinged beam transmits force, shares displacement, and has two end rotations', () => {
    const model = example('hinge');
    const left = solve(model, 'AB', 1), right = solve(model, 'BC', 0);
    assert.equal(left.kind, 'solution');
    assert.equal(right.kind, 'solution');
    for (const side of [left, right]) assert.deepEqual(side.readouts[2], zero);
    assert.deepEqual(left.readouts.slice(4), right.readouts.slice(4));
    assert.ok(!equal(left.readouts[3], right.readouts[3]));
    // Load is 20 kN at midspan of the 4 m suspended span.
    assert.deepEqual(left.reactions.slice(0, 3), [zero, integer(10), integer(40)]);
    assert.deepEqual(left.reactions[7], integer(10));
    assert.deepEqual(solve(model, 'BC', 0.5).readouts[2], integer(20));
});

test('a couple on one hinge face does work only on its selected end rotation', () => {
    for (const [member, t, leftMoment, rightMoment] of [['AB', 1, 8, 0], ['BC', 0, 0, -8]]) {
        const model = example('hinge');
        model.loads = [{ id: 'C', kind: 'moment', member, t, end: 1, fx: 0, fy: 0, mz: 8, qEnd: 0 }];
        assert.deepEqual(solve(model, 'AB', 1).readouts[2], integer(leftMoment));
        assert.deepEqual(solve(model, 'BC', 0).readouts[2], integer(rightMoment));
    }
});

test('removing the suspended span roller produces a loaded mechanism candidate', () => {
    const model = example('hinge');
    model.supports.pop();
    const result = solve(model, 'BC', 0.5);
    assert.equal(result.kind, 'mechanism');
    assert.ok(!equal(result.loadWork, zero));
});
