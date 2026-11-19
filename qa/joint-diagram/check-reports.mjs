import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { compareJointDiagram } from '../member-diagram/member-diagram-joint-student-cases.mjs';

for (const stiffness of [0, 2500, 5000]) {
    for (const load of ['point', 'affine']) {
        for (const member of ['AB', 'BC']) {
            const file = '.data/joint-diagram/' + [stiffness, load, member].join('-') + '.packet.report';
            const [protocol, hexMember, ...rows] = (await readFile(file, 'utf8')).split('\n');
            assert.equal(protocol, 'CV2011_DIAGRAM_1');
            assert.equal(hexMember, [...member].map(c => c.charCodeAt(0).toString(16).padStart(4, '0')).join(''));
            const observed = { pieces: [], candidates: [] };
            for (const line of rows) {
                const [field, ...fields] = line.split(' ');
                if (field === 'P') {
                    const [start, end] = fields;
                    observed.pieces.push({ start, end, shear:fields.slice(2,6).join(','), moment:fields.slice(6).join(',') });
                } else {
                    const [pieceIndex, side, xLow, xHigh, yLow, yHigh, min, max] = fields;
                    observed.candidates.push({field, pieceIndex, side, xLow, xHigh, yLow, yHigh,
                        min:String(min === '1'), max:String(max === '1')});
                }
            }
            compareJointDiagram(observed, load === 'point' ? 'nodal' : 'affine', stiffness ? 'spring'+stiffness : 'hinge', member);
            console.log('Matched hand calculation', file);
        }
    }
}
