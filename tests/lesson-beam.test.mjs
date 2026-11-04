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
const { beamDrawing, reactionEquations, sectionEquations } = await import('../web/lesson-view.ts');
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
    for (const load of ['NaN', 'Infinity', '-4', '99999', ''])
        assert.equal(lessonContext(`?lesson=beam-basics&load=${load}`).model.loads[0].fy, -20);
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
