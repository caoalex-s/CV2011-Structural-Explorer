import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
import { example } from '../web/engine.ts';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { pointForceRules } = await import('../web/point-force-rules.ts');

test('parameterized point force follows magnitude, label, sign and section crossing', () => {
    const model = example('beam');
    model.loads[0].label = 'F_A';
    for (const [position, force, after, shear, moment] of [[0.25, -20, true, -5, 20], [0.75, -40, false, 10, 40], [0.5, 0, true, 0, 0], [0.5, 20, true, 10, -40]]) {
        model.loads[0].t = position; model.loads[0].fy = force;
        const rule = pointForceRules(model, 0.5);
        assert.equal(rule.after, after); assert.equal(rule.shear, shear); assert.equal(rule.moment, moment);
        assert.equal(rule.label, 'F_{A}'); assert.equal(rule.maximum, force <= 0);
    }
});

test('inapplicable geometry, support, load family, joints, and out-of-span loads are rejected', () => {
    const mutations = [m => m.loads[0].t = -0.01, m => m.loads[0].t = 1.01, m => m.loads[0].fx = 1,
        m => m.loads[0].kind = 'distributed', m => m.supports[1].t = 0.9,
        m => m.supports[1].angle = 45, m => m.nodes[1].y = 1,
        m => m.nodes[0].joint = 'pinned', m => m.loads.push({...m.loads[0], id: 'other'})];
    for (const mutate of mutations) { const model = example('beam'); mutate(model); assert.equal(pointForceRules(model, 0.5), null); }
});


test('endpoint point forces use the support and one-sided section limits', () => {
    const model = example('beam');
    model.loads[0].t = 0;
    assert.equal(pointForceRules(model, 0).shear, 0);
    model.loads[0].t = 1;
    const rightLimit = pointForceRules(model, 1);
    assert.equal(rightLimit.after, false);
    assert.equal(rightLimit.shear, 0);
    assert.equal(rightLimit.moment, 0);
});
