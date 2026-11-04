import test from 'node:test';
import assert from 'node:assert/strict';
import { compactEquationHtml, equationHtml, math, methodRules, numberLatex, rationalLatex } from '../web/math.ts';

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

test('short evaluations retain arithmetic, SI conversion, and approximate equality', () => {
    const rendered = compactEquationHtml({
        label:'v', labelLatex:'v(4)', latex:String.raw`-\frac{40}{3}`,
        exact:'-40/3', unit:'mm', symbolicLatex:String.raw`-\frac{5wL^4}{384EI}`,
        symbolicUnit:'m', substitutionLatex:String.raw`-\frac{5\times8^4\times5}{384\times20000}`,
    });
    assert.doesNotMatch(rendered, /math-error/);
    assert.match(rendered, /20000/);
    assert.match(rendered, /approx/);
    assert.match(rendered, /13\.3333/);
    assert.match(rendered, /\\mathrm\{m\}/);
    assert.match(rendered, /\\mathrm\{mm\}/);
    const roundedFraction = compactEquationHtml({
        label:'x', labelLatex:'x', latex:'1/99999999999999999999',
        exact:'1/99999999999999999999', unit:'m',
    });
    assert.match(roundedFraction, /approx/);
});


test('numeric substitutions use LaTeX powers of ten, including signed exponents', () => {
    assert.equal(numberLatex(-4e-7), String.raw`-4\times10^{-7}`);
    assert.equal(numberLatex(3e21), String.raw`3\times10^{21}`);
    assert.equal(numberLatex(0), '0');
    assert.equal(numberLatex(-12.34567), '-12.3457');
    for (const value of [-4e-7, 3e21, 0, -12.34567])
        assert.doesNotMatch(math(numberLatex(value)), /math-error/);
});
