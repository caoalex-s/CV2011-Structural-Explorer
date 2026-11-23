/** Independent Week 04 Example 1 benchmark from the lecture geometry.
 * Forces are in kN, coordinates in m. An axial coefficient multiplies the
 * full end-to-end vector, avoiding roundoff from the 45-degree diagonal.
 */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

const drawing = JSON.parse(readFileSync(new URL(
    './course-examples/week-04-section-truss.drawing.json', import.meta.url
), 'utf8'));

const difference = (first, second) => [second.x - first.x, second.y - first.y];
const counterclockwiseMoment = (point, centre, fx, fy) =>
    (point.x - centre.x) * fy - (point.y - centre.y) * fx;

function components(point, centre, [fx, fy]) {
    return [fx, fy, counterclockwiseMoment(point, centre, fx, fy)];
}

function determinant([a, b, c]) {
    return a[0] * (b[1] * c[2] - b[2] * c[1]) -
        a[1] * (b[0] * c[2] - b[2] * c[0]) +
        a[2] * (b[0] * c[1] - b[1] * c[0]);
}

function solveThreeColumns(columns, rightHandSide) {
    const denominator = determinant(columns);
    assert.notEqual(denominator, 0, 'The section equilibrium equations are dependent');
    return columns.map((_, selected) => {
        const numerator = determinant(columns.map((column, index) =>
            index === selected ? rightHandSide : column
        ));
        return numerator === 0 ? 0 : numerator / denominator;
    });
}

function sumColumns(columns) {
    return columns.reduce((sum, values) => sum.map((value, i) => value + values[i]), [0, 0, 0]);
}

export function sectionReference({ load = 1, cut = 3, side = 'left', centre = 'G' } = {}) {
    const joints = Object.fromEntries(drawing.joints.map(joint => [joint.id, joint]));
    const momentCentre = joints[centre];
    assert.ok(momentCentre && ['left', 'right'].includes(side));
    const applied = [0, load === 0 ? 0 : -load];

    // Reactions follow from the whole-truss free body. Taking moments about D
    // eliminates both pin reactions and leaves the roller reaction.
    const supportColumns = [
        components(joints.D, joints.D, [1, 0]),
        components(joints.D, joints.D, [0, 1]),
        components(joints.E, joints.D, [1, 0])
    ];
    const reactions = solveThreeColumns(supportColumns,
        components(joints.A, joints.D, applied).map(value => -value)
    );
    const forcesAtSupports = [
        { joint: 'D', name: 'Dx', force: [reactions[0], 0], direction: [1, 0] },
        { joint: 'D', name: 'Dy', force: [0, reactions[1]], direction: [0, 1] },
        { joint: 'E', name: 'Ex', force: [reactions[2], 0], direction: [1, 0] }
    ];

    const retained = point => side === 'left' ? point.x < cut : point.x > cut;
    const kept = drawing.joints.filter(retained).map(point => point.id);
    const crossed = drawing.bars.filter(([a, b]) => retained(joints[a]) !== retained(joints[b]));
    const external = [
        { joint: 'A', name: 'P', force: applied, direction: [0, -1] },
        ...forcesAtSupports
    ].filter(action => kept.includes(action.joint)).map(action => ({
        ...action,
        symbolic: components(joints[action.joint], momentCentre, action.direction),
        substituted: components(joints[action.joint], momentCentre, action.force)
    }));

    const cutActions = crossed.map(([a, b]) => {
        const [near, far] = retained(joints[a]) ? [a, b] : [b, a];
        const direction = difference(joints[near], joints[far]);
        const x = cut;
        const y = joints[near].y + (x - joints[near].x) * direction[1] / direction[0];
        return {
            member: a + b,
            retained: near,
            cutPoint: [x, y],
            direction,
            lengthSquared: direction[0] ** 2 + direction[1] ** 2,
            column: components(joints[near], momentCentre, direction)
        };
    });

    const externalSum = sumColumns(external.map(action => action.substituted));
    const columns = cutActions.map(action => action.column);
    const coefficients = columns.length === 3 ?
        solveThreeColumns(columns, externalSum.map(value => -value)) : null;
    const forces = coefficients && cutActions.map((action, index) => {
        const coefficient = coefficients[index];
        return {
            member: action.member,
            coefficient,
            value: coefficient * Math.sqrt(action.lengthSquared),
            state: coefficient > 0 ? 'T' : coefficient < 0 ? 'C' : 'zero'
        };
    });
    return {
        load, cut, side, centre, kept, cutActions, external, externalSum, forces,
        reactions: Object.fromEntries(forcesAtSupports.map((entry, i) => [entry.name, reactions[i]]))
    };
}
