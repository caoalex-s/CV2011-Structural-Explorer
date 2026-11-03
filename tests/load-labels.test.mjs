import test from 'node:test';
import assert from 'node:assert/strict';
import { example } from '../web/engine.ts';
import { assignLoadLabels, loadLabels, validLoadLabel, resolveLoadNotation } from '../web/load-labels.ts';
import { findPublishedExample } from '../web/published-worked.ts';
import { equationHtml } from '../web/math.ts';
import { symbolLabel } from '../web/symbols.ts';

test('force, moment, and intensity symbols remain distinct after editing the model', () => {
    const model = example('beam');
    model.loads.push({...model.loads[0], id:'m', kind:'moment'}, {...model.loads[0], id:'w', kind:'distributed'});
    assignLoadLabels(model);
    assert.deepEqual([...loadLabels(model).values()], ['P_1','M_0','w_1']);
    model.loads.push({...model.loads[0], id:'next', label:undefined});
    assignLoadLabels(model);
    model.loads.shift();
    assignLoadLabels(model);
    assert.equal(model.loads.at(-1).label, 'P_2');
    assert.equal(validLoadLabel('M_0','moment'), true);
    assert.equal(validLoadLabel('P_1<script>','force'), false);
    assert.equal(validLoadLabel('EI','force'), false);
    assert.match(symbolLabel('P_A = 20 kN'), /<tspan baseline-shift="sub"/);
    assert.match(symbolLabel('w_1,a = 2'), /font-size="75%">1,<tspan class="svg-variable">a<\/tspan><\/tspan>/);
    assert.doesNotMatch(symbolLabel('P_A <script>'), /<script>/);
});

test('diagram annotations distinguish mathematical symbols from prose and units', () => {
    const reaction = symbolLabel('AAᵧ = 20 kN');
    assert.match(reaction, /class="svg-variable">AA<\/tspan>/);
    assert.match(reaction, /baseline-shift="sub".*class="svg-variable">y<\/tspan>/);
    assert.doesNotMatch(reaction, /ᵧ/);
    const peak = symbolLabel('Peak |M| = 40 kN m');
    assert.match(peak, /^Peak \|<tspan class="svg-variable">M<\/tspan>\| = 40 kN m$/);
    assert.match(symbolLabel('M(A) = 10 kN m'), /class="svg-variable">A<\/tspan>/);
    assert.doesNotMatch(symbolLabel('P_A <script>alert(1)</script> & "x"'), /<script>|& "/);
});

test('renaming a load preserves the public solution and updates all notation safely', () => {
    const original = example('beam');
    const renamed = structuredClone(original);
    renamed.loads[0].label = 'F_A';
    const entry = {model:original, solutions:[]};
    assert.equal(findPublishedExample(renamed, {examples:[entry]}), entry);
    const row = resolveLoadNotation({label:'Reaction', labelLatex:'B_y',
        symbolicLatex:String.raw`\frac{\loadsymbol{0}{}}{2}`, latex:'10', exact:'10', unit:'kN'}, renamed);
    assert.equal(row.symbolicLatex, String.raw`\frac{F_{A}}{2}`);
    assert.doesNotMatch(equationHtml(row), /math-error|loadsymbol/);
    assert.equal(resolveLoadNotation(String.raw`\loadsymbol{0}{y}`, renamed), 'F_{A,y}');
});
