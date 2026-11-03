import test from 'node:test';
import assert from 'node:assert/strict';
import { equationHtml, math, methodRules, rationalLatex } from '../web/math.ts';

test('all course method rules render as accessible LaTeX', () => {
    for (const [name, source] of Object.entries(methodRules)) {
        const rendered = math(source, true);
        assert.doesNotMatch(rendered, /math-error/, name);
        assert.match(rendered, /katex-html/, name);
        assert.match(rendered, /<math/, name);
    }
});

test('computed equations preserve exact fractions, subscripts, and units', () => {
    const rendered = equationHtml({
        label: 'v(xₛ)', labelLatex: 'v(x_s)', latex: rationalLatex('-32/3'),
        exact: '-32/3', unit: 'mm',
    });
    assert.doesNotMatch(rendered, /math-error/);
    assert.match(rendered, /<mfrac>/);
    assert.match(rendered, /<msub>/);
    assert.match(rendered, /mm/);
});

test('equation rendering does not allow links or HTML injection', () => {
    assert.doesNotMatch(math(String.raw`\href{https://example.invalid}{click}`), /<a\b|href=/);
    const failed = math(String.raw`\unsupported{<img src=x onerror=alert(1)>}`);
    assert.match(failed, /math-error/);
    assert.doesNotMatch(failed, /<img/);
    assert.match(failed, /&lt;img/);
});
