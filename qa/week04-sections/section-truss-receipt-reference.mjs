/** Receipt expectations derived from an independent whole-truss and cut balance. */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { sectionReference } from './section-truss-reference.mjs';

const sourceDrawing = JSON.parse(readFileSync(new URL(
    './course-examples/week-04-section-truss.drawing.json', import.meta.url
), 'utf8'));

export const sha = bytes => createHash('sha256').update(bytes).digest('hex');

function gcd(a, b) {
    while (b !== 0) [a, b] = [b, a % b];
    return a;
}

function term(name, column, divisor, magnitude) {
    const [x, y, m] = column.map(value => value / divisor);
    return [name, x, y, m, x * x + y * y, magnitude].join(',');
}

export function expectedSectionPackets(query) {
    const reference = sectionReference(query);
    assert.ok(reference.forces && reference.cut === 3);
    const { cut, side, centre, load } = reference;
    const source = structuredClone(sourceDrawing);
    source.joints.find(joint => joint.id === 'A').fy = load ? -load : 0;
    const jointLines = source.joints.map(joint => [
        joint.id, joint.x, joint.y, joint.support, joint.rx, joint.ry, joint.fx, joint.fy
    ].join(','));
    const barLines = source.bars.map(pair => pair.join(','));
    const packet = ['SECTION1', cut, side, centre, 'TRUSS1', source.joints.length, ...jointLines, ...barLines].join('\n');
    const cutTermLines = reference.cutActions.map((action, i) => {
        const divisor = gcd(Math.abs(action.direction[0]), Math.abs(action.direction[1]));
        return term(action.member, action.column, divisor, reference.forces[i].coefficient * divisor);
    });
    const externalTermLines = reference.external.map(action =>
        term(action.name, action.symbolic, 1, action.name === 'P' ? load : reference.reactions[action.name])
    );
    const reactions = Object.entries(reference.reactions).map(([name, value]) => [name, value].join(','));
    const report = ['SECTION1', [cut, side, centre, load].join(','), ...cutTermLines, ...externalTermLines,
        ...reactions, 'SUM,0,0,0'].join('\n');
    return { source, packet, report, reference };
}
