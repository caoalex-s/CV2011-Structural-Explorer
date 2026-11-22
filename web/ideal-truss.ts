import { integer, zero, one, div, mul, neg, sub, dot } from './frame-rational.js';
import type { Fraction } from './frame-rational.js';
export type Joint = {
    id: string;
    x: number;
    y: number;
    support: 'free' | 'pin' | 'roller';
    rx: number;
    ry: number;
    fx: number;
    fy: number;
};
export type Drawing = {
    kind: 'ideal-planar-truss';
    joints: Joint[];
    bars: [string, string][];
};
export const joint = (id: string, x: number, y: number): Joint => ({ id, x, y, support: 'free', rx: 0, ry: 1, fx: 0, fy: 0 });
export function rectangle(): Drawing {
    const joints = [joint('A', 0, 0), joint('B', 4, 0), joint('C', 4, 3), joint('D', 0, 3)];
    joints[0].support = 'pin';
    joints[1].support = 'roller';
    joints[2].fx = 4;
    return { kind: 'ideal-planar-truss', joints, bars: [['A', 'B'], ['B', 'C'], ['C', 'D'], ['D', 'A'], ['A', 'C']] };
}
export function validate(d: Drawing) {
    if (d.kind !== 'ideal-planar-truss' || !Array.isArray(d.joints) || !Array.isArray(d.bars) || d.joints.length > 26 || d.bars.length > 64)
        throw Error('Use up to 26 joints and 64 bars.');
    const ids = new Set<string>(), positions = new Set<string>(), edges = new Set<string>();
    for (const j of d.joints) {
        if (!/^[A-Z]$/.test(j.id) || ids.has(j.id) || positions.has([j.x, j.y].join()))
            throw Error('Each joint needs a distinct letter and position.');
        if (![j.x, j.y, j.fx, j.fy, j.rx, j.ry].every(n => Number.isSafeInteger(n) && Math.abs(n) <= 1000))
            throw Error('Use whole numbers between −1000 and 1000.');
        if (!['free', 'pin', 'roller'].includes(j.support) || (j.support === 'roller' && !j.rx && !j.ry))
            throw Error('Specify a nonzero roller reaction direction.');
        ids.add(j.id);
        positions.add([j.x, j.y].join());
    }
    for (const [a, b] of d.bars) {
        const key = [a, b].sort().join();
        if (a === b || !ids.has(a) || !ids.has(b) || edges.has(key))
            throw Error('Connect two distinct joints with one bar.');
        edges.add(key);
    }
}
export const number = (v: Fraction) => Number(v.n) / Number(v.d);
export const exact = (v: Fraction) => v.d === 1n ? String(v.n) : v.n + '/' + v.d;
type Column = {
    name: string;
    length: number;
    entries: number[];
};
/** A bar unknown is force per unit length. This keeps all direction coefficients exact. */
export function solve(d: Drawing) {
    validate(d);
    const { joints, bars } = d, size = 2 * joints.length;
    const columns: Column[] = [];
    for (const [a, b] of bars) {
        const i = joints.findIndex(j => j.id === a), k = joints.findIndex(j => j.id === b);
        const dx = joints[k].x - joints[i].x, dy = joints[k].y - joints[i].y;
        const entries = Array(size).fill(0);
        entries[2 * i] = dx;
        entries[2 * i + 1] = dy;
        entries[2 * k] = -dx;
        entries[2 * k + 1] = -dy;
        columns.push({ name: a + b, length: Math.hypot(dx, dy), entries });
    }
    joints.forEach((j, i) => {
        const directions = j.support === 'pin' ? [[1, 0], [0, 1]] : j.support === 'roller' ? [[j.rx, j.ry]] : [];
        for (const [x, y] of directions) {
            const entries = Array(size).fill(0);
            entries[2 * i] = x;
            entries[2 * i + 1] = y;
            columns.push({ name: j.id + (x === 1 && !y ? 'x' : !x && y === 1 ? 'y' : 'r'), length: Math.hypot(x, y), entries });
        }
    });
    const width = columns.length, loads = joints.flatMap(j => [integer(j.fx), integer(j.fy)]);
    // The identity block tracks row combinations. Each zero equilibrium row yields
    // a permitted motion, including the virtual work of the original joint loads.
    const rows = loads.map((load, i) => [...columns.map(c => integer(c.entries[i])), neg(load), ...loads.map((_, k) => i === k ? one : zero)]);
    const pivots: number[] = [];
    for (let col = 0; col < width; col++) {
        const r = pivots.length, k = rows.findIndex((row, i) => i >= r && row[col].n !== 0n);
        if (k < 0)
            continue;
        [rows[r], rows[k]] = [rows[k], rows[r]];
        const pivot = rows[r][col];
        rows[r] = rows[r].map(v => div(v, pivot));
        for (let i = 0; i < size; i++)
            if (i !== r && rows[i][col].n !== 0n) {
                const factor = rows[i][col];
                rows[i] = rows[i].map((v, j) => sub(v, mul(factor, rows[r][j])));
            }
        pivots.push(col);
    }
    const rank = pivots.length;
    const motions = rows.slice(rank).map(row => {
        const u = row.slice(width + 1);
        return { u, work: dot(u, loads) };
    });
    const compatible = motions.every(m => m.work.n === 0n);
    const unique = compatible && rank === width && rank === size;
    const forces = unique ? columns.map((c, i) => ({ ...c, coefficient: rows[pivots.indexOf(i)][width], value: number(rows[pivots.indexOf(i)][width]) * c.length })) : null;
    return { columns, rank, motions, compatible, forces, redundancy: width - rank };
}
/** Match the complete source assumptions of the three Lean theorems.
    Endpoint order, array order and the load parameter may vary. */
export function rectangleCase(d: Drawing) {
    const ref = rectangle();
    if (d.joints.length !== 4)
        return;
    for (const j of ref.joints) {
        const v = d.joints.find(v => v.id === j.id);
        if (!v || v.x !== j.x || v.y !== j.y || v.support !== j.support || v.fy !== 0 || (j.id !== 'C' && v.fx !== 0))
            return;
    }
    const edges = new Set(d.bars.map(pair => [...pair].sort().join('')));
    if (!['AB', 'BC', 'CD', 'AD'].every(e => edges.has(e)))
        return;
    const b = d.joints.find(j => j.id === 'B')!;
    if (edges.size === 4 && b.rx === 0 && b.ry === 1)
        return 'unbraced';
    if (edges.size === 5 && edges.has('AC')) {
        if (b.rx === 0 && b.ry === 1)
            return 'braced';
        if (b.rx === 1 && b.ry === 0)
            return 'horizontal';
    }
}
