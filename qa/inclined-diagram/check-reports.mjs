import { readFile } from 'node:fs/promises';
import { parseInclinedDiagram, compareInclinedDiagram } from './member-diagram-inclined-student-cases.mjs';
import { affineInclinedCantilever, inclinedJumpCantilever, inclinedHingeSpan, inclinedSpringSpan }
    from './member-diagram-inclined-reference.mjs';

const cases = [
    ['jump', 'AB', inclinedJumpCantilever()], ['release', 'BC', inclinedHingeSpan()],
    ['spring-forward', 'BC', inclinedSpringSpan()], ['spring-reverse', 'BC', inclinedSpringSpan(true)],
];
for (const height of [2, 3]) {
    for (const reverse of [false, true]) {
        cases.push(['h' + height + (reverse ? '-reverse' : '-forward'), 'AB', affineInclinedCantilever(height, reverse)]);
    }
}
for (const [name, member, reference] of cases) {
    const bytes = await readFile('.data/inclined-diagram/' + name + '.packet.report', 'utf8');
    const observed = parseInclinedDiagram(bytes, member);
    compareInclinedDiagram(observed, reference);
    console.log(name, observed.pieces.length, 'pieces,', observed.candidates.length, 'candidate rows');
}
