import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { bindIntervalDisplay, renderIntervalValues } = await import('../web/frame-interval-display.ts');
const { frameQueryConvention } = await import('../web/frame-candidate.ts');
const rational = (numerator, denominator = '1') => ({ numerator, denominator });

function fixture() {
    // Representation only: these arbitrary intervals do not certify this model.
    const model = {
        nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 1, y: 2 }],
        members: [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }],
        supports: [{ id: 'S', member: 'AB', kind: 'fixed', t: 0, angle: 90 }],
        loads: [{ id: 'P', member: 'AB', kind: 'force', t: 0.5, end: 0.5, fx: 3, fy: -7, mz: 0, qEnd: 0 }],
    };
    const query = { member: 'AB', parameter: 0.5, cutSide: 'left', ...frameQueryConvention };
    const value = { lower: rational('1', '3'), upper: rational('1'), midpoint: rational('2', '3') };
    const point = (owner, index, id, parameter) => ({ owner, index, id, parameter,
        reactions: Array.from({ length: 3 }, () => structuredClone(value)) });
    const values = { query: { member: 'AB', parameter: rational('1', '2'), cutSide: 'left', convention: 1 },
        fields: Array.from({ length: 6 }, () => structuredClone(value)),
        points: [point('node', 0, 'A', rational('0')), point('node', 1, 'B', rational('0')),
            point('member', 0, 'AB', rational('1', '2'))] };
    return { model, query, values };
}

test('display binding covers query side, source point ownership, and complete inventory', () => {
    const { model, query, values } = fixture();
    assert.doesNotThrow(() => bindIntervalDisplay(model, query, values));
    for (const mutate of [
        value => { value.query.cutSide = 'right'; },
        value => { value.query.parameter = rational('1', '3'); },
        value => { value.points[2].owner = 'node'; },
        value => { value.points[2].index = 1; },
        value => { value.points[2].id = 'A'; },
        value => { value.points[2].parameter = rational('1', '3'); },
        value => { value.points.pop(); },
    ]) {
        const changed = structuredClone(values); mutate(changed);
        assert.throws(() => bindIntervalDisplay(model, query, changed), /differs|differ/);
    }
});

test('exact enclosures remain visible and rounded results have a separate evidence label', () => {
    const { values } = fixture();
    values.query.member = '<img src=x onerror=alert(1)>';
    values.points[0].id = '<script>bad</script>';
    const html = renderIntervalValues(values);
    assert.match(html, /data-evidence="exact-midpoint"[^>]*>2\/3</);
    assert.match(html, /data-evidence="exact-enclosure"[^>]*>\[1\/3, 1\]</);
    assert.match(html, /data-evidence="rounded-midpoint">≈ 0\.666667</);
    assert.match(html, /additional decimal rounding error/);
    assert.match(html, /10⁻¹⁰ rad/);
    assert.match(html, /10⁻⁹ m/);
    assert.doesNotMatch(html, /<script>|<img /);
    assert.match(html, /&lt;script&gt;/);
    assert.equal((html.match(/data-evidence="exact-enclosure"/g) ?? []).length, 15);
});
