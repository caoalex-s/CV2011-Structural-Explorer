/** Compare actual Lean report bytes with the separately logged native intervals.
 * Run: node qa/inclined-frame/verify-reports.mjs PACKET_DIRECTORY NATIVE_LOG
 * This exercises representation only; physical references are checked in Python.
 */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { registerHooks } from 'node:module';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { decodeAcceptedIntervalReport } = await import('../../web/frame-interval-result.ts');
const [directory, nativeLog] = process.argv.slice(2);
assert(directory && nativeLog, 'Supply packet directory and native log.');
const manifest = JSON.parse(readFileSync(resolve(directory, 'manifest.json'), 'utf8'));
const nativeCases = new Map();
let current;
for (const line of readFileSync(nativeLog, 'utf8').split(/\r?\n/)) {
    const caseLine = /^case=(\S+) accepted=(true|false) expected=(true|false) elapsed_ms=\d+$/.exec(line);
    if (caseLine) {
        assert.equal(caseLine[2], caseLine[3]);
        assert(!nativeCases.has(caseLine[1]), 'Repeated native case.');
        current = { accepted: caseLine[2] === 'true', intervals: [] };
        nativeCases.set(caseLine[1], current);
    } else if (/^(field|point)=/.test(line)) {
        assert(current?.accepted, 'Output without an accepted native case.');
        const interval = / interval=(-?\d+\/\d+),(-?\d+\/\d+)$/.exec(line);
        assert(interval, 'Malformed native interval.');
        current.intervals.push(interval.slice(1));
    }
}
assert.deepEqual([...nativeCases.keys()].sort(), manifest.map(item => item.name).sort());
const rationalText = value => `${value.numerator}/${value.denominator}`;
let reports = 0;
for (const fixture of manifest) {
    const native = nativeCases.get(fixture.name);
    assert.equal(native.accepted, fixture.expected === 'accept');
    if (!native.accepted) continue;
    const values = decodeAcceptedIntervalReport(readFileSync(resolve(directory, fixture.name + '.report')));
    const intervals = [...values.fields, ...values.points.flatMap(point => point.reactions)];
    assert.deepEqual(intervals.map(value => [rationalText(value.lower), rationalText(value.upper)]),
        native.intervals, fixture.name);

    // Independently known fixture identities and one-sided query parameters.
    const shared = fixture.name === 'shared-rigid-joint';
    const roller = fixture.name.startsWith('roller-interior-');
    const interior = fixture.name.includes('interior') || fixture.name === 'affine-zero-resultant';
    const reversedEnd = fixture.name === 'reversed-cantilever';
    assert.equal(values.query.member, shared ? 'BC' : 'AB');
    assert.equal(rationalText(values.query.parameter), interior ? '1/2' : reversedEnd ? '0/1' : '1/1');
    assert.equal(values.query.cutSide, reversedEnd || fixture.name.endsWith('-right') ? 'right' : 'left');
    const identities = values.points.map(point => [point.owner, point.index, point.id, rationalText(point.parameter)]);
    const expected = [['node', 0, 'A', '0/1'], ['node', 1, 'B', '0/1']];
    if (shared) expected.push(['node', 2, 'C', '0/1']);
    if (roller) expected.push(['member', 0, 'AB', '1/2']);
    assert.deepEqual(identities, expected, fixture.name);
    reports++;
}
assert.equal(reports, 8);
console.log(`${reports} actual Lean reports preserve native intervals, exact midpoints and source identities`);
