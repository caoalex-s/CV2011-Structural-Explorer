import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';

registerHooks({resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
}});
const {rectangle, rectangleCase, solve} = await import('../web/ideal-truss.ts');
const {agrees, packet} = await import('../web/truss-check.ts');
const encode = text => new TextEncoder().encode(text);

test('Force agreement rejects a sign change, a load edit and extra report rows', () => {
    const model = rectangle();
    // P = 4. Bar unknowns are axial force divided by length, in drawing order.
    const lines = ['TRUSS1','8','F,0,1','F,-1,1','F,0,1','F,0,1','F,1,1','F,-4,1','F,-3,1','F,3,1'];
    const report = encode(lines.join('\n'));
    assert.ok(agrees(model, report));
    assert.equal(agrees(model, encode([...lines,'F,0,1'].join('\n'))), false);
    assert.equal(agrees(model, encode(lines.join('\n').replace('F,-1,1','F,1,1'))), false);
    const original = packet(model);
    model.joints[2].fx = -4;
    assert.notDeepEqual(packet(model), original);
    assert.equal(agrees(model, report), false);
});

test('Mechanism agreement requires the same nonzero scaling of velocity and work', () => {
    const model = rectangle();
    model.bars.pop();
    const report = row => encode('TRUSS1\n7\nM,' + row);
    assert.ok(agrees(model,report('-8,0,0,0,0,2,0,2,0')));
    assert.equal(agrees(model,report('8,0,0,0,0,2,0,2,0')),false);
    assert.equal(agrees(model,report('0,0,0,0,0,0,0,0,0')),false);
});

test('Reference theorem selection depends on the entire load and support pattern', () => {
    const model = rectangle();
    model.bars.reverse().forEach(bar => bar.reverse());
    assert.equal(rectangleCase(model),'braced');
    model.joints[0].fy = 1;
    assert.equal(rectangleCase(model),undefined);
    model.joints[0].fy = 0;
    model.joints[1].rx = 1;
    assert.equal(rectangleCase(model),undefined);
    assert.equal(solve(model).rank,8);
});
