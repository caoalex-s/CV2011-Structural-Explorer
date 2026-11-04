import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
import { example } from '../web/engine.ts';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
globalThis.fetch = async () => ({ok: true, json: async () => ({lean: 'checked'})});
const { pointForceWorked } = await import('../web/point-force-worked.ts');
const { pointForceDerivation } = await import('../web/worked.ts');

test('offline derivation renders both branches and a renamed action', () => {
    const model = example('beam'); model.loads[0].label = 'F_A';
    for (const position of [0, 0.25, 0.75, 1]) for (const force of [-20, 0, 20]) {
        model.loads[0].t = position; model.loads[0].fy = force;
        const html = pointForceDerivation(pointForceWorked(model, 0.5));
        assert.doesNotMatch(html, /math-error/);
        assert.match(html, /Double integration/);
        assert.match(html, /Moment-area and virtual work/);
        assert.match(html, /no Lean certificate/);
        assert.match(html, /F_\{A\}/);
    }
});

test('elastic solution rejects invalid rigidity and unsupported models', () => {
    const model = example('beam'); model.members[0].EI = 0;
    assert.equal(pointForceWorked(model, 0.5), null);
    model.members[0].EI = 20000; model.loads[0].kind = 'distributed';
    assert.equal(pointForceWorked(model, 0.5), null);
});
