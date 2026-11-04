import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
import { analyse } from '../web/engine.ts';
import { beamValues, lessonBeam, lessonContext } from '../web/lesson-beam.ts';

const webDirectory = new URL('../web/', import.meta.url).href;
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.startsWith(webDirectory) && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { beamDrawing, cutDrawing, cutEquations, reactionEquations, sectionEquations } = await import('../web/lesson-view.ts');
const { lessonText } = await import('../web/lesson-content.ts');
const near = (actual, expected) => assert.ok(Math.abs(actual - expected) < 1e-7 * Math.max(1, Math.abs(expected)), `${actual} != ${expected}`);

test('lesson formulas agree with the frame engine across the activity range', () => {
    for (const load of [5, 20, 50]) for (const span of [4, 8, 12]) for (const position of [0.1, 0.25, 0.5, 0.9]) {
        const inputs = { load, span, position }, result = analyse(lessonBeam(inputs));
        assert.equal(result.status, 'stable'); assert.equal(result.degree, 0);
        const values = beamValues(inputs);
        near(result.reactions[0].fy, values.left); near(result.reactions[1].fy, values.right);
        for (const element of result.elements) for (const sample of element.samples) {
            // At the force each element has its own one-sided shear value.
            const expected = beamValues(inputs, sample.t);
            near(sample.M, expected.moment); near(sample.N, 0);
            if (Math.abs(sample.t - position) > 1e-9) near(sample.V, expected.shear);
        }
        near(beamValues(inputs, 0).moment, 0); near(beamValues(inputs, 1).moment, 0);
        near(beamValues(inputs, position).moment, values.peak);
    }
});

test('constraint activity distinguishes count, geometry, and redundancy', () => {
    const expected = { 'pin-roller': ['stable', 0], 'two-rollers': ['unstable'], 'three-rollers': ['unstable'], 'fixed-roller': ['stable', 1] };
    for (const [name, [status, degree]] of Object.entries(expected)) {
        const result = analyse(lessonBeam(undefined, name));
        assert.equal(result.status, status);
        if (degree !== undefined) assert.equal(result.degree, degree);
    }
});

test('lesson handoff is bounded and does not reuse the sandbox storage key', () => {
    assert.equal(lessonContext('?load=30'), null);
    assert.equal(lessonContext('?lesson=unknown'), null);
    const valid = lessonContext('?lesson=beam-basics&load=30&span=8&position=0.25');
    assert.equal(valid.model.loads[0].fy, -30); assert.equal(valid.model.loads[0].t, 0.25);
    assert.notEqual(valid.storageKey, 'cv2011-model');
    assert.equal(lessonContext('?position=0.25&span=8&load=30&lesson=beam-basics').storageKey, valid.storageKey);
    assert.notEqual(lessonContext('?lesson=beam-basics').storageKey, valid.storageKey);
    for (const load of ['NaN', 'Infinity', '-4', '99999', ''])
        assert.equal(lessonContext(`?lesson=beam-basics&load=${load}`).model.loads[0].fy, -20);
});

test('retained free bodies include the load only after it and agree with the equilibrium branch', () => {
    const inputs = {load: 20, span: 8, position: 0.5};
    assert.doesNotMatch(cutDrawing(inputs, 0.25), /data-cut-load/);
    for (const section of [0.5, 0.75]) {
        const drawing = cutDrawing(inputs, section);
        assert.match(drawing, /data-cut-load="P"/);
        assert.doesNotMatch(drawing, /support-stroke/);
        assert.match(cutEquations(inputs, section), /P\(x-a\)/);
        assert.doesNotMatch(cutEquations(inputs, section), /math-error/);
    }
    assert.match(cutDrawing(inputs, 0.5), /right-hand cut/);
});

test('constant diagram scales expose load and span changes while automatic fitting remains optional', () => {
    const heights = (load, span, scale) => {
        const svg = beamDrawing({load, span, position: 0.5}, 0.5, false, 'pin-roller', true, scale);
        const peakY = Number(/M100 450L380 ([\d.]+)/.exec(svg)[1]);
        const shearY = Number(/M100 285V([\d.]+)/.exec(svg)[1]);
        return [peakY - 450, 285 - shearY];
    };
    const baseline = heights(20, 8, 'constant');
    assert.deepEqual(heights(40, 8, 'constant'), baseline.map(value => value * 2));
    assert.deepEqual(heights(20, 4, 'constant'), [baseline[0] / 2, baseline[1]]);
    assert.deepEqual(heights(20, 8, 'automatic'), heights(40, 8, 'automatic'));
});

test('authored prediction math is typeset while prose markup is escaped', () => {
    const rendered = lessonText('Reaction $A_y = P(L-a)/L$ <script>unsafe</script>');
    assert.match(rendered, /class="katex"/);
    assert.match(rendered, /&lt;script&gt;/);
    assert.doesNotMatch(rendered, /math-error|<script>/);
});

test('lesson equations render and diagram-side changes preserve vector origins', () => {
    for (const position of [0.1, 0.5, 0.9]) {
        const inputs = { load: 30, span: 8, position };
        for (const section of [0.1, 0.5, 0.9]) {
            assert.doesNotMatch(reactionEquations(inputs) + sectionEquations(inputs, section), /math-error/);
            const origins = svg => [...svg.matchAll(/data-origin-x="([^"]+)" data-origin-y="([^"]+)"/g)].map(match => match.slice(1));
            assert.deepEqual(origins(beamDrawing(inputs, section)), origins(beamDrawing(inputs, section, true)));
        }
    }
});
