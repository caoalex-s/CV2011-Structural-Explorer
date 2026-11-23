import type { Drawing } from './ideal-truss.js';
import { diagram } from './week04-figures.js';
import { members, type Query, type CheckedSection, type Term } from './week04-section.js';
const mark = (n: number) => String(n).replace('-', '−');
function force(c: number, r: number) {
    if (r === 1 || !c)
        return mark(c);
    return (c < 0 ? '−' : '') + (Math.abs(c) === 1 ? '' : Math.abs(c)) + '√' + r;
}
function symbol(t: Term) {
    return ['P', 'Dx', 'Dy', 'Ex'].includes(t.name) ? t.name.replace(/([xy])/, '<sub>$1</sub>') : 'F<sub>' + t.name + '</sub>';
}
function equation(axis: 'x' | 'y' | 'moment', terms: Term[], centre: string) {
    const moment = axis === 'moment', units = moment ? 'kN·m' : 'kN';
    const parts = terms.filter(t => t[axis] !== 0);
    const expression = (numeric: boolean) => parts.map((t, i) => {
        const a = t[axis], abs = Math.abs(a);
        const sign = a < 0 ? '−' : i ? ' + ' : '';
        const coefficient = moment ? '(' + abs + ' m)' : abs !== 1 ? String(abs) : '';
        const value = numeric ? '(' + force(t.component, t.radicand) + ' kN)' : symbol(t);
        return sign + coefficient + value + (t.radicand === 1 ? '' : '/√' + t.radicand);
    }).join(' ');
    const name = moment ? 'ΣM<sub>' + centre + '</sub>' : 'ΣF<sub>' + axis + '</sub>';
    return `<div data-equation="${axis}"><p>${name} = ${expression(false)} = 0</p><p>${expression(true)} = 0 ${units}</p></div>`;
}
export function solution(d: Drawing, q: Query, a: CheckedSection) {
    const { terms, reactions: r, p } = a;
    const point = (id: string) => d.joints.find(j => j.id === id)!;
    const span = point('D').x - point('A').x, height = point('D').y - point('E').y;
    const bc = terms.find(t => t.name === 'BC')!, diagonal = terms.find(t => t.name === 'GC')!, gf = terms.find(t => t.name === 'GF')!;
    const order: ('moment' | 'y' | 'x')[] = q.centre === 'G' ? ['moment', 'y', 'x'] : ['y', 'moment', 'x'];
    return `<h2>Equilibrium of the ${q.side} section</h2>${diagram(d, q, a)}
    <p>The cut arrows point away from the retained body. Each member force is positive in tension. External arrows show the applied load or the calculated reactions.</p>
    <h3>Support reactions</h3><p>Take right, up and anticlockwise as positive. On the whole truss, ΣM<sub>D</sub> = (${span} m)P + (${height} m)E<sub>x</sub> = 0. With P = ${mark(p)} kN, E<sub>x</sub> = ${mark(r.Ex)} kN.</p>
    <p>ΣF<sub>x</sub> = D<sub>x</sub> + E<sub>x</sub> = 0 gives D<sub>x</sub> = ${mark(r.Dx)} kN. ΣF<sub>y</sub> = D<sub>y</sub> − P = 0 gives D<sub>y</sub> = ${mark(r.Dy)} kN.</p>
    <h3>Section equations</h3><p>${q.centre === 'G' ? 'The lines of action of GC and GF pass through G. Take moments about G to obtain BC, then use vertical and horizontal equilibrium.' : 'Use vertical equilibrium to find GC. Substitute its vertical and horizontal components into the moment and horizontal force equations.'}</p>
    ${order.map(axis => equation(axis, terms, q.centre)).join('')}
    <p>The vertical equation gives F<sub>GC</sub>/√2 = P, so F<sub>GC</sub> = √2 P = ${force(diagonal.component, diagonal.radicand)} kN. The moment and horizontal equations then give F<sub>BC</sub> = P = ${mark(bc.component)} kN and F<sub>GF</sub> = −2P = ${mark(gf.component)} kN.</p>
    <table class="data-table"><thead><tr><th>Member</th><th>Signed axial force</th><th>Magnitude and sense</th></tr></thead><tbody>${members.map(name => {
        const t = terms.find(v => v.name === name)!;
        const sense = t.component > 0 ? 'T' : t.component < 0 ? 'C' : 'zero';
        return `<tr data-member="${name}" data-component="${t.component}" data-radicand="${t.radicand}" data-sense="${sense}"><th>${name}</th><td>${force(t.component, t.radicand)} kN</td><td>${force(Math.abs(t.component), t.radicand)} kN ${sense === 'T' ? 'tension' : sense === 'C' ? 'compression' : '(zero force)'}</td></tr>`;
    }).join('')}</tbody></table>
    <details><summary>Checked equation coefficients</summary><p>Multiply each row by its signed force divided by its direction length. Moment coefficients are in metres.</p><table class="data-table"><thead><tr><th>Force</th><th>x</th><th>y</th><th>Moment about ${q.centre}</th><th>Direction length</th></tr></thead><tbody>${terms.map(t => `<tr data-term="${t.name}" data-x="${t.x}" data-y="${t.y}" data-moment="${t.moment}" data-component="${t.component}" data-radicand="${t.radicand}"><th>${symbol(t)}</th><td>${mark(t.x)}</td><td>${mark(t.y)}</td><td>${mark(t.moment)} m</td><td>${force(1, t.radicand)}</td></tr>`).join('')}</tbody></table></details>`;
}
