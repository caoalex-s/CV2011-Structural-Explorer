/** Decode and verify the whole-member kinematics wire report independently
 * of the application renderer. A union of displayed location intervals is
 * a cover of the extrema, including each side of every source split.
 */
import assert from 'node:assert/strict';
import { enclosesReference } from './member-diagram-inclined-reference.mjs';

export const deformationProtocol = 'CV2011_MEMBER_KINEMATICS_1';
const rational = /^-?\d+\/[1-9]\d*$/;
const fieldName = { S: 'theta', D: 'v' };

function compareRatio(first, second) {
    const [a, b] = first.split('/').map(BigInt);
    const [c, d] = second.split('/').map(BigInt);
    const difference = a*d-c*b;
    return difference < 0n ? -1 : difference > 0n ? 1 : 0;
}

function readBox(lower, upper) {
    assert.match(lower, rational);
    assert.match(upper, rational);
    assert.ok(compareRatio(lower, upper) <= 0, 'Reversed interval');
    return [lower, upper];
}

function number(ratio) {
    const [top, bottom] = ratio.split('/').map(BigInt);
    const scale = 10n ** 20n;
    return Number(top * scale / bottom) / Number(scale);
}

function union(intervals) {
    const ordered = [...intervals].sort((first, second) => compareRatio(first[0], second[0]));
    const joined = [];
    for (const box of ordered) {
        const previous = joined.at(-1);
        if (!previous || compareRatio(previous[1], box[0]) < 0) {
            joined.push([...box]);
        } else if (compareRatio(previous[1], box[1]) < 0) {
            previous[1] = box[1];
        }
    }
    return joined;
}

export function parseDeformationReport(report, memberId) {
    const [protocol, identifier, ...records] = report.split('\n');
    assert.equal(protocol, deformationProtocol);
    assert.equal(identifier, Array.from({ length: memberId.length }, (_, i) =>
        memberId.charCodeAt(i).toString(16).padStart(4, '0')).join(''));
    const pieces = [], extrema = {}, locations = [];
    for (const text of records) {
        const [tag, ...tokens] = text.split(' ');
        if (tag === 'P') {
            assert.equal(tokens.length, 11);
            const [index, a, b, angle0lo, angle0hi, angle1lo, angle1hi, v0lo, v0hi, v1lo, v1hi] = tokens;
            assert.equal(index, String(pieces.length));
            assert.match(a, rational);
            assert.match(b, rational);
            assert.ok(compareRatio(a, b) < 0);
            pieces.push({
                a, b,
                theta: { start: readBox(angle0lo, angle0hi), end: readBox(angle1lo, angle1hi) },
                v: { start: readBox(v0lo, v0hi), end: readBox(v1lo, v1hi) },
            });
            continue;
        }
        const field = fieldName[tag];
        assert.ok(field, 'Unexpected field ' + tag);
        const [kind, ...values] = tokens;
        if (kind === 'bounds') {
            assert.equal(values.length, 4);
            assert.equal(extrema[field], undefined);
            const [minLo, minHi, maxLo, maxHi] = values;
            extrema[field] = { min: readBox(minLo, minHi), max: readBox(maxLo, maxHi) };
        } else {
            assert.equal(kind, 'location');
            assert.equal(values.length, 5);
            const [index, min, max, lower, upper] = values;
            assert.match(index, /^\d+$/);
            assert.ok(Number(index) < pieces.length);
            assert.ok([min, max].every(flag => flag === '0' || flag === '1') && (min === '1' || max === '1'));
            locations.push({ field, index: Number(index), min: min === '1', max: max === '1',
                x: readBox(lower, upper) });
        }
    }
    assert.ok(pieces.length > 0);
    assert.ok(extrema.theta && extrema.v);
    return { pieces, extrema, locations };
}

export function compareDeformationReport(observed, reference) {
    assert.equal(observed.pieces.length, reference.pieces.length);
    for (const [index, piece] of observed.pieces.entries()) {
        const expected = reference.pieces[index];
        assert.deepEqual([piece.a, piece.b], [expected.a, expected.b]);
        for (const field of ['theta', 'v']) {
            for (const side of ['start', 'end']) {
                const ref = reference.candidates.find(row => row.index === index && row.field === field && row.side === side);
                assert.ok(enclosesReference(piece[field][side], ref.value), `${field} ${side} misses the member-face value`);
            }
        }
    }

    for (const location of observed.locations) {
        const piece = reference.pieces[location.index];
        const [lo, hi] = location.x.map(number);
        assert.ok(lo >= number(piece.start[0])-1e-8 && hi <= number(piece.end[1])+1e-8,
            'Location lies outside its source piece');
    }
    for (const field of ['theta', 'v']) {
        for (const flag of ['min', 'max']) {
            const box = observed.extrema[field][flag];
            assert.ok(number(box[1])-number(box[0]) <= 1.01e-8, field + ' ' + flag + ' is too wide');
            const refs = reference.candidates.filter(row => row.field === field && row[flag]);
            assert.ok(refs.length);
            for (const target of refs) {
                assert.ok(enclosesReference(box, target.value), `${field} ${flag} misses the hand ordinate`);
                const boxes = observed.locations.filter(row => row.field === field && row.index === target.index && row[flag])
                    .map(row => row.x);
                assert.ok(union(boxes).some(interval => enclosesReference(interval, target.x)),
                    `${field} ${flag} loses a location at piece ${target.index}`);
            }
        }
    }
}
