/** Source-derived proposals for the admissible coordinates at one rigid point.
 * Distinct exact angle classes constrain both translations, however close their
 * numerical normals are. Formal row-space equivalence must be established separately. */
import type { Support } from './engine.js';
import { binary64, zero, one, equal } from './frame-rational.js';
import { IntervalArithmetic, type RationalInterval } from './frame-interval.js';
import { degreeAxes, degreeClass } from './frame-interval-geometry.js';

export interface PointBasisColumn {
    coordinate: 'x' | 'y' | 'tangent' | 'rotation';
    components: [RationalInterval, RationalInterval, RationalInterval];
}

/** The caller retains source ownership and supplies ALL supports at this point. */
export function pointBasis(arithmetic: IntervalArithmetic, supports: readonly Support[]) {
    if (supports.length > 16) throw Error('Limit: at most 16 supports per point.');
    if (supports.some(support => !['pin', 'fixed', 'roller'].includes(support.kind)))
        throw Error('Unsupported: enclosure supports must be fixed, pin or roller.');
    const classes: { angle: ReturnType<typeof degreeClass>; sourceIndices: number[] }[] = [];
    supports.forEach((support, sourceIndex) => {
        if (support.kind !== 'roller') return;
        const angle = degreeClass(binary64(support.angle), 180);
        const existing = classes.find(group => equal(group.angle, angle));
        if (existing) existing.sourceIndices.push(sourceIndex);
        else classes.push({ angle, sourceIndices: [sourceIndex] });
    });
    const columns: PointBasisColumn[] = [];
    const z = () => arithmetic.bounds(zero), u = () => arithmetic.bounds(one);
    const translationBlocked = supports.some(support => support.kind === 'fixed' || support.kind === 'pin') || classes.length >= 2;
    if (!translationBlocked && classes.length === 0) {
        columns.push({ coordinate: 'x', components: [u(), z(), z()] });
        columns.push({ coordinate: 'y', components: [z(), u(), z()] });
    } else if (!translationBlocked) {
        const normal = degreeAxes(arithmetic, classes[0].angle);
        columns.push({ coordinate: 'tangent', components: [arithmetic.negate(normal.sine), normal.cosine, z()] });
    }
    if (!supports.some(support => support.kind === 'fixed'))
        columns.push({ coordinate: 'rotation', components: [z(), z(), u()] });
    return { classes, columns, sourceSupportCount: supports.length };
}
