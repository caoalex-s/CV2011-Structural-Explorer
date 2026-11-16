import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { createIntervalExplanation, renderIntervalExplanation } = await import('../web/frame-interval-worked.ts');
const { frameQueryConvention } = await import('../web/frame-candidate.ts');
const rat = (numerator, denominator = '1') => ({ numerator, denominator });

test('inclined teaching substitutions recover independent cantilever equilibrium without claiming accuracy', () => {
    const model = {
        nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 1, y: 2 }],
        members: [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }],
        supports: [{ id: 'S', member: 'AB', kind: 'fixed', t: 0, angle: 90 }],
        loads: [{ id: 'P', member: 'AB', kind: 'force', t: 1, end: 1, fx: 3, fy: -7, mz: 0, qEnd: 0 }],
    };
    const query = { member: 'AB', parameter: 0.5, cutSide: 'left', ...frameQueryConvention };
    // Only the representation and source identity are exercised here. Zero
    // intervals are synthetic and are not evidence of physical containment.
    const zero = { lower: rat('0'), upper: rat('0'), midpoint: rat('0') };
    const values = { query: { member: 'AB', parameter: rat('1', '2'), cutSide: 'left', convention: 1 },
        fields: Array.from({ length: 6 }, () => structuredClone(zero)),
        points: ['A', 'B'].map((id, index) => ({ owner: 'node', index, id, parameter: rat('0'),
            reactions: Array.from({ length: 3 }, () => structuredClone(zero)) })) };
    const explanation = createIntervalExplanation(model, query, values);
    assert.equal(explanation.evidence, 'explanatory-numerical');
    assert.equal('state' in explanation, false);
    const { a1, a2, a3, x } = explanation.inputs;
    assert.ok(Math.abs(-a1 + 11 / Math.sqrt(5)) < 1e-10);
    assert.ok(Math.abs(a2 - 13 / Math.sqrt(5)) < 1e-10);
    assert.ok(Math.abs(-a3 + a2 * x + 6.5) < 1e-10);
    const html = renderIntervalExplanation(explanation, values);
    assert.doesNotMatch(html, /katex-error/);
    assert.match(html, /do not inherit the accuracy guarantee/);
    assert.match(html, /data-evidence="explanatory-numerical"/);
    assert.match(html, /data-evidence="exact-enclosure"/);
    assert.match(html, /kN\/m²/);
});
