import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { registerHooks } from 'node:module';
registerHooks({resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
}});
const { decodeInclinedReleaseReport } = await import('../../web/frame-inclined-release-result.ts');
// The tip couple is transmitted through both members independently of their
// inclination. Its spring rotation is 10/k, in addition to the elastic rotation
// of the 4 m reference member (10×4/EI). All comparisons use exact rationals.
function contains(interval, numerator, denominator = 1) {
    const n = BigInt(numerator), d = BigInt(denominator);
    assert.ok(BigInt(interval.lower.numerator) * d <= n * BigInt(interval.lower.denominator));
    assert.ok(n * BigInt(interval.upper.denominator) <= BigInt(interval.upper.numerator) * d);
}

for (const k of [10000, 20000]) {
    for (const rise of [0, 2]) {
        const filename = '.data/frame-spring/' + k + '-' + rise + '.packet.report';
        const report = decodeInclinedReleaseReport(await readFile(filename), true);
        assert.equal(report.springs.length, 1);
        const spring = report.springs[0];
        assert.equal(spring.side, 2);
        contains(spring.relativeRotation, 10, k);
        contains(spring.transmittedMoment, 10);
        contains(report.faces.find(face => face.member === 'AB').rotation, 1, 500);
        contains(report.faces.find(face => face.member === 'BC').rotation, k + 5000, 500 * k);
        contains(report.fields[2], 10);
        const support = report.points.find(point => point.id === 'A');
        contains(support.reactions[0], 0);
        contains(support.reactions[1], 0);
        contains(support.reactions[2], -10);
    }
}
