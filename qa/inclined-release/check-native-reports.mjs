import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { registerHooks } from 'node:module';
registerHooks({resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
}});
const { decodeInclinedReleaseReport } = await import('../../web/frame-inclined-release-result.ts');
const number = rational => Number(rational.numerator) / Number(rational.denominator);
function enclosed(interval, expected) {
    const tolerance = 1e-12 * Math.max(1, Math.abs(expected));
    assert.ok(number(interval.lower) <= expected + tolerance && expected - tolerance <= number(interval.upper),
        `Expected ${expected} within [${number(interval.lower)}, ${number(interval.upper)}]`);
}
// With the only couple applied on a fixed released end, the restraint takes
// that couple directly. It does no work on the other end's rotation.
const fixedEnd = decodeInclinedReleaseReport(await readFile('.data/inclined-release/fixed-at-release.packet.report'));
for (const face of fixedEnd.faces) {
    enclosed(face.rotation, 0);
    enclosed(face.moment, 0);
}
enclosed(fixedEnd.points.find(point => point.id === 'B').reactions[2], -10);
for (const field of fixedEnd.fields) enclosed(field, 0);
for (const direction of ['forward', 'reverse']) {
    for (const loaded of [false, true]) {
        const name = direction + (loaded ? '-couple' : '');
        const result = decodeInclinedReleaseReport(await readFile('.data/inclined-release/' + name + '.packet.report'));
        const a = result.points.find(p => p.id === 'A'), c = result.points.find(p => p.id === 'C');
        const reactionA = loaded ? [-5, 5, 20] : [-10, 0, 0];
        const reactionC = loaded ? [5, 5, 0] : [10, 10, 0];
        reactionA.forEach((value, i) => enclosed(a.reactions[i], value));
        reactionC.forEach((value, i) => enclosed(c.reactions[i], value));
        const expected = [loaded ? Math.sqrt(5) : 20/Math.sqrt(5), (loaded ? 15 : 10)/Math.sqrt(5),
            loaded ? (direction === 'forward' ? -10 : 10) : 0];
        expected.forEach((value, i) => enclosed(result.fields[i], value));
        const [reference, released] = result.faces;
        assert.equal(reference.released, false);
        assert.equal(released.released, true);
        assert.deepEqual(reference.ux, released.ux);
        assert.deepEqual(reference.uy, released.uy);
        enclosed(reference.moment, 0);
        enclosed(released.moment, expected[2]);
        console.log('Verified hand reactions and member-side results:', name);
    }
}
