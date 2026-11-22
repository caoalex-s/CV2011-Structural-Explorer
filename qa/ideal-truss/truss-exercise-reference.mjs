/** Independent exact references for the CV2011 rectangular-truss exercise.
 * Joint order is A, B, C, D, with x and y interleaved. Signed axial forces
 * are positive in tension. The synthetic load P acts horizontally at C.
 */

const joints = { A: [0n, 0n], B: [4n, 0n], C: [4n, 3n], D: [0n, 3n] };
const perimeter = ['AB', 'BC', 'CD', 'DA'];
const jointOrder = Object.keys(joints);

/** Each column is five times a unit action, so all matrix entries are
 * integers, including those for the 3–4–5 diagonals. */
function memberColumn(name) {
    const [start, end] = name.split('');
    const [xStart, yStart] = joints[start];
    const [xEnd, yEnd] = joints[end];
    const dx = xEnd - xStart;
    const dy = yEnd - yStart;
    const [x, y] = dx === 0n ? [0n, 5n * dy / 3n] :
        dy === 0n ? [5n * dx / 4n, 0n] : [dx, dy];
    return jointOrder.flatMap(joint => joint === start ? [x, y] : joint === end ? [-x, -y] : [0n, 0n]);
}

function actionAt(joint, x, y) {
    return jointOrder.flatMap(name => name === joint ? [x, y] : [0n, 0n]);
}

function dot(left, right) {
    return left.reduce((sum, term, index) => sum + term * right[index], 0n);
}

/** Exact rank by clearing each pivot during row elimination. The matrix
 * has eight rows, so intermediate integers remain small for these cases. */
function rank(columns) {
    const rows = Array.from({ length: columns[0]?.length ?? 0 }, (_, index) => columns.map(column => column[index]));
    let pivotRow = 0;
    for (let column = 0; column < columns.length && pivotRow < rows.length; column++) {
        const pivot = rows.findIndex((row, index) => index >= pivotRow && row[column] !== 0n);
        if (pivot < 0) continue;
        [rows[pivot], rows[pivotRow]] = [rows[pivotRow], rows[pivot]];
        const basis = rows[pivotRow];
        for (let index = pivotRow + 1; index < rows.length; index++) {
            const factor = rows[index][column];
            if (factor === 0n) continue;
            rows[index] = rows[index].map((value, offset) => basis[column] * value - factor * basis[offset]);
        }
        pivotRow++;
    }
    return pivotRow;
}

function fourths(numerator) {
    if (numerator % 4n === 0n) return (numerator / 4n) + '/1';
    if (numerator % 2n === 0n) return (numerator / 2n) + '/2';
    return numerator + '/4';
}

/** Return a hand equilibrium solution and motion where they apply. The load
 * may be any signed integer in kN, including a reversed or zero load. */
export function rectangleTrussReference({ brace = true, redundant = false, roller = 'vertical', load = 12 } = {}) {
    if (!['vertical', 'horizontal'].includes(roller)) throw new RangeError('Use a vertical or horizontal reaction');
    const P = BigInt(load);
    const bars = [...perimeter, ...(brace ? ['AC'] : []), ...(redundant ? ['BD'] : [])];
    const barColumns = bars.map(memberColumn);
    const reactionColumns = [actionAt('A', 5n, 0n), actionAt('A', 0n, 5n),
        roller === 'vertical' ? actionAt('B', 0n, 5n) : actionAt('B', 5n, 0n)];
    const columns = [...barColumns, ...reactionColumns];
    const force = actionAt('C', P, 0n);
    const equilibriumRank = rank(columns);
    const equilibriumExists = rank([...columns, force]) === equilibriumRank;
    const uniqueEquilibrium = equilibriumExists && columns.length === equilibriumRank;
    const rows = 2 * jointOrder.length;
    const mechanismCount = rows - equilibriumRank;
    const selfStressCount = columns.length - equilibriumRank;
    const rigidRotation = jointOrder.flatMap(name => [-joints[name][1], joints[name][0]]);
    const rigidTranslations = [jointOrder.flatMap(() => [1n, 0n]), jointOrder.flatMap(() => [0n, 1n])];
    const rigidSupportRank = rank(reactionColumns.map(column => [...rigidTranslations, rigidRotation]
        .map(rigidMotion => dot(column, rigidMotion))));
    const noBrace = !brace && !redundant;
    const motions = [];
    if (noBrace) motions.push({ name: 'sway of the upper edge', vector: [0n, 0n, 0n, 0n, 1n, 0n, 1n, 0n] });
    if (roller === 'horizontal') {
        motions.push({ name: 'rigid rotation about A', vector: rigidRotation });
    }
    for (const { vector } of motions) {
        if (columns.some(column => dot(column, vector) !== 0n)) throw Error('Reference motion violates a constraint');
    }
    // Moments about A give 4 B_y = 3 P. At joint C the x balance gives
    // 4 N_AC / 5 = P; its y balance gives N_BC = -3 N_AC / 5.
    const forces = {};
    const reactions = {};
    if (uniqueEquilibrium && brace && !redundant) {
        const memberFourths = { AB: 0n, BC: -3n * P, CD: 0n, DA: 0n, AC: 5n * P };
        const reactionFourths = [-4n * P, -3n * P, 3n * P];
        const values = [...bars.map(bar => memberFourths[bar]), ...reactionFourths];
        // Columns multiply unit actions by five; values multiply forces by four.
        for (const [row, component] of force.entries()) {
            if (dot(columns.map(column => column[row]), values) + 20n * component !== 0n) {
                throw Error('Hand forces violate joint equilibrium');
            }
        }
        bars.forEach(bar => { forces[bar] = fourths(memberFourths[bar]); });
        ['Ax', 'Ay', 'By'].forEach((name, index) => { reactions[name] = fourths(reactionFourths[index]); });
    }
    return {
        joints: jointOrder.length, bars: bars.length, reactionComponents: reactionColumns.length,
        countDifference: columns.length - rows, equilibriumRank, barRank: rank(barColumns),
        rigidSupportRank, mechanismCount, selfStressCount, equilibriumExists, uniqueEquilibrium,
        motions: motions.map(({ name, vector }) => ({ name, vector: vector.map(Number), work: String(dot(force, vector)) })),
        reactions, forces,
    };
}
