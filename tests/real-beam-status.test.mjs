import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
import { example } from '../web/engine.ts';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { realPointForceApplies } = await import('../web/real-beam-status.ts');
const receipt = { status: 'checked', theoremSet: 'point-force-real-fields-v1', sourceSha256: 'a'.repeat(64) };

test('real-field label follows the checked theorem set and physical family', () => {
    const model = example('beam');
    for (const position of [0, 0.25, 0.5, 0.75, 1]) for (const force of [-30, 0, 20]) {
        model.loads[0].t = position; model.loads[0].fy = force;
        assert.equal(realPointForceApplies(model, 0.5, receipt), true);
    }
    for (const changed of [{...receipt, status: 'pending'}, {...receipt, sourceSha256: ''},
                           {...receipt, theoremSet: 'other'}])
        assert.equal(realPointForceApplies(model, 0.5, changed), false);
    const edits = [m => m.supports[1].t = 0.8, m => m.loads[0].kind = 'moment',
        m => m.loads[0].fx = 1, m => m.members[0].EI = 0, m => m.nodes[1].y = 1,
        m => m.nodes[0].joint = 'pinned', m => m.members[0].EA = 0,
        m => m.loads[0].qEnd = Number.NaN, m => m.supports[0].angle = Number.NaN,
        m => m.nodes[1].x = 0.01];
    for (const edit of edits) { const altered = structuredClone(model); edit(altered); assert.equal(realPointForceApplies(altered, 0.5, receipt), false); }
});
