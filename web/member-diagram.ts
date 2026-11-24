/** Render the compiled checker's report. Rational endpoints remain available in the
 * table and receipt; only the SVG drawing is converted to screen coordinates. */
import { math, measureUnits, numberLatex, quantity, rationalLatex } from './math.js';

type Field = 'V' | 'M';
interface Piece { start: string; end: string; V: string[]; M: string[] }
interface Row { field: Field; piece: number; side: string; x: string[]; y: string[]; min: boolean; max: boolean }
const unit = { V: 'kN', M: 'kN m' };
const rational = (s: string) => /^-?(?:0|[1-9]\d*)\/[1-9]\d*$/.test(s);
const exact = (s: string) => s.endsWith('/1') ? s.slice(0, -2) : s;
const exactLatex = (s: string) => rationalLatex(exact(s));
const intensityUnit = String.raw`\mathrm{kN/m}`;
const gradientUnit = String.raw`\mathrm{kN/m^2}`;
const loadProjection = `For a piece from member fraction ${math('a')} to ${math('b')}, the signed vertical intensity is ${math('f_y = -w')} for a downward-positive load ${math('w')}. Its end intensities give ${math(String.raw`B=(b-a)\Delta X f_{y,0}`)} and ${math(String.raw`C=(b-a)\Delta X(f_{y,1}-f_{y,0})/2`)}.`;
const differentialRelations = `Integrating ${math(String.raw`\mathrm{d}V/\mathrm{d}x=q`)} and ${math(String.raw`\mathrm{d}M/\mathrm{d}x=V`)} gives`;
function approximate(s: string): number {
    const [a, b] = s.split('/').map(BigInt);
    if (a === 0n) return 0;
    const digits = (a < 0n ? -a : a).toString(), divisor = b.toString();
    const mantissa = (v: string) => Number(v[0] + '.' + v.slice(1,17));
    return (a < 0n ? -1 : 1) * mantissa(digits) / mantissa(divisor) * 10 ** (digits.length - divisor.length);
}
function bounds(pair: string[], flat = false): string {
    if (pair[0] === pair[1]) return exact(pair[0]);
    if (flat) return `[${exact(pair[0])}, ${exact(pair[1])}]`;
    // Round outward for the displayed interval as well as retaining exact bytes.
    const endpoints = pair.map((s, i) => {
        const [a, b] = s.split('/').map(BigInt);
        const scaled = a * 1000000n, remainder = scaled % b;
        const rounded = scaled / b + (i === 0 && remainder < 0n ? -1n : i === 1 && remainder > 0n ? 1n : 0n);
        const magnitude = (rounded < 0n ? -rounded : rounded).toString().padStart(7, '0');
        return (rounded < 0n ? '−' : '') + magnitude.slice(0,-6) + '.' + magnitude.slice(-6);
    });
    return '[' + endpoints.join(', ') + ']';
}
function formula(coeff: string[]): string {
    const terms = coeff.flatMap((s, power) => {
        if (s === '0/1') return [];
        const [n,d] = s.replace(/^-/, '').split('/');
        const magnitude = d === '1' ? n : `\\frac{${n}}{${d}}`;
        const variable = power === 0 ? '' : power === 1 ? '\\xi' : `\\xi^{${power}}`;
        return [(s.startsWith('-') ? '-' : '+') + (variable && magnitude === '1' ? '' : magnitude) + variable];
    });
    return terms.join('').replace(/^\+/, '') || '0';
}
function plot(field: Field, pieces: Piece[], rows: Row[]): string {
    const length = approximate(pieces.at(-1)!.end);
    const peak = Math.max(...rows.flatMap(row => row.y.map(s => Math.abs(approximate(s))))) || 1;
    const curves = pieces.map(piece => {
        const a = approximate(piece.start), b = approximate(piece.end), h = b-a;
        const [c0,c1,c2,c3] = piece[field].map(approximate);
        return [a,b,c0,h*c1,h*h*c2,h*h*h*c3];
    });
    return drawPlot(field,length,peak,curves);
}
function drawPlot(field: Field, length: number, peak: number, curves: number[][]): string {
    const x = (v: number) => 52 + v / length * 564;
    const y = (v: number) => 88 - v / peak * 60;
    // Cubic Bézier end tangents reproduce each polynomial in the affine plot
    // coordinates. Each one-sided piece gets its own path at a jump.
    let drawable = Number.isFinite(length) && length > 0 && Number.isFinite(peak);
    const paths = curves.map(([a,b,c0,c1,c2,c3]) => {
        const h = b-a;
        const right = c0+c1+c2+c3;
        const slope = c1+2*c2+3*c3;
        const controls = [x(a),y(c0),x(a+h/3),y(c0+c1/3),x(b-h/3),y(right-slope/3),x(b),y(right)];
        if (!controls.every(Number.isFinite)) drawable = false;
        return `<path d="M ${controls.slice(0,2).join(' ')} C ${controls.slice(2).join(' ')}" fill="none" stroke="#087f78" stroke-width="2.5"/>`;
    }).join('');
    if (!drawable) return '<p>The drawing scale exceeds the plotting range. The table gives the checked values.</p>';
    return `<svg viewBox="0 0 650 188" role="img" aria-label="${field} diagram, positive upward, distance along the member in metres" style="width:100%;max-width:650px"><path d="M52 17V155 M52 88H616" fill="none" stroke="currentColor" opacity=".5"/><text x="8" y="15">${field} (${unit[field]})</text><text x="47" y="177">0</text><text x="612" y="177" text-anchor="end">${length.toPrecision(5)} m</text>${paths}</svg>`;
}
export function renderMemberDiagram(bytes: Uint8Array, member: string, label: string, cosine: number): HTMLElement {
    const lines = new TextDecoder('utf-8', {fatal:true}).decode(bytes).split('\n');
    const id = Array.from({length:member.length}, (_, i) => member.charCodeAt(i).toString(16).padStart(4,'0')).join('');
    if (bytes.length > 262144 || lines.shift() !== 'CV2011_DIAGRAM_1' || lines.shift() !== id)
        throw Error('Diagram report does not match the selected member.');
    const pieces: Piece[] = [], rows: Row[] = [];
    for (const line of lines) {
        const [tag,...fields] = line.split(' ');
        if (tag === 'P' && fields.length === 10 && fields.every(rational)) {
            pieces.push({start:fields[0],end:fields[1],V:fields.slice(2,6),M:fields.slice(6)});
        } else if ((tag === 'V' || tag === 'M') && fields.length === 8 && /^\d+$/.test(fields[0]) &&
            Number(fields[0]) < pieces.length && ['start','end','interior','flat'].includes(fields[1]) &&
            fields.slice(2,6).every(rational) && fields.slice(6).every(v => v === '0' || v === '1')) {
            rows.push({field:tag,piece:Number(fields[0]),side:fields[1],x:fields.slice(2,4),y:fields.slice(4,6),
                min:fields[6]==='1',max:fields[7]==='1'});
        } else throw Error('Invalid whole-member diagram record.');
    }
    if (!pieces.length || !rows.length) throw Error('Empty diagram report.');
    const section = document.createElement('section');
    section.id = 'checked-member-diagram';
    const title = document.createElement('h3');
    title.textContent = 'Checked shear and bending moment diagrams · ' + label;
    section.append(title);
    const equation = math(String.raw`V=V_0+q_0\xi+g\xi^2/2,\qquad M=M_0+V_0\xi+q_0\xi^2/2+g\xi^3/6`, true);
    section.insertAdjacentHTML('beforeend', `<p>Measure ${math('x')} in metres from the first drawn end. On each interval starting at ${math('a')}, ${math(String.raw`\xi=x-a`)}. The signed transverse load is ${math(String.raw`q(\xi)=q_0+g\xi`)}, with ${math('q_0')} in ${math(intensityUnit)} and ${math('g')} in ${math(gradientUnit)}. ${loadProjection} ${differentialRelations}</p>` + equation);
    const direction = cosine === 1 ? `For this rightward horizontal member, positive editor load ${math('w')} acts downwards, so ${math('q=-w')}.` :
        cosine === -1 ? `For this leftward horizontal member, positive editor load ${math('w')} acts in the positive local transverse direction, so ${math('q=w')}.` :
        'On this vertical member, the vertical distributed load has zero transverse component.';
    const sign = document.createElement('p'); sign.innerHTML = direction; section.append(sign);
    pieces.forEach((p, i) => {
        const [n,d] = p.V[2].split('/').map(BigInt);
        const gradient = d % 2n === 0n ? n + '/' + (d / 2n) : (2n*n) + '/' + d;
        const parameter = (name: string, value: string, units: string) => math(name + '=' + quantity(exactLatex(value), units));
        const parameters = `Using ${parameter('V_0', p.V[0], measureUnits.force)}, ${parameter('M_0', p.M[0], measureUnits.moment)}, ${parameter('q_0', p.V[1], intensityUnit)} and ${parameter('g', gradient, gradientUnit)}, substitute ${math(String.raw`\xi=x-(${quantity(exactLatex(p.start), measureUnits.length)})`)}.`;
        section.insertAdjacentHTML('beforeend', `<div data-piece="${i}" data-start="${p.start}" data-end="${p.end}" data-shear="${p.V}" data-moment="${p.M}"><h4>Interval ${exact(p.start)} to ${exact(p.end)} m</h4><p>${parameters}</p>${math(`V(\\xi)=${formula(p.V)}\\;\\mathrm{kN},\\qquad M(\\xi)=${formula(p.M)}\\;\\mathrm{kN\\,m}`,true)}</div>`);
    });
    for (const field of ['V','M'] as const) {
        const entries = rows.filter(row => row.field === field);
        section.insertAdjacentHTML('beforeend', `<h4>${field==='V'?'Shear force':'Bending moment'}</h4>`+plot(field,pieces,entries)+
            `<p>Both plots use positive values upwards. Interior candidates satisfy ${math(field === 'V' ? 'q=0' : 'V=0')}.</p>`+
            `<table><thead><tr><th>Member side</th><th>${math('x')} (m)</th><th>${math(field)} (${unit[field]})</th><th>Whole-member extremum</th></tr></thead><tbody>`+
            entries.map(r => `<tr data-candidate data-field="${field}" data-side="${r.side}" data-piece-index="${r.piece}" data-x-low="${r.x[0]}" data-x-high="${r.x[1]}" data-y-low="${r.y[0]}" data-y-high="${r.y[1]}" data-min="${r.min}" data-max="${r.max}"><td>${({start:'Right-hand limit',end:'Left-hand limit',flat:'Constant interval',interior:'Stationary point'})[r.side]}</td><td>${bounds(r.x,r.side==='flat')}</td><td>${bounds(r.y)}</td><td>${[r.min?'Minimum':'',r.max?'Maximum':''].filter(Boolean).join(' and ')||'—'}</td></tr>`).join('')+'</tbody></table>');
    }
    return section;
}

/** A box encloses the physical value. Only the illustrative drawing uses its midpoint. */
export function renderInclinedMemberDiagram(bytes: Uint8Array, member: string, label: string, dx: number, dy: number): HTMLElement {
    const lines = new TextDecoder('utf-8', { fatal: true }).decode(bytes).split('\n');
    const hex = Array.from({length:member.length}, (_,i) => member.charCodeAt(i).toString(16).padStart(4,'0')).join('');
    if (bytes.length > 262144 || lines.shift() !== 'CV2011_INCLINED_DIAGRAM_1' || lines.shift() !== hex)
        throw Error('Inclined diagram report does not match the drawing.');
    const section = document.createElement('section');
    section.id = 'checked-member-diagram';
    const title = document.createElement('h3');
    title.textContent = 'Checked shear and bending moment diagrams · ' + label;
    section.append(title);
    const description = document.createElement('p');
    const axisSpan = (axis: string, length: number) => math(String.raw`\Delta ${axis}=${quantity(numberLatex(length, 17), measureUnits.length)}`);
    description.innerHTML = `The drawn member has ${axisSpan('X', dx)} and ${axisSpan('Y', dy)}. Its length is ${math(String.raw`L=\sqrt{(\Delta X)^2+(\Delta Y)^2}`)}. Measure ${math('x')} from its first end. On each piece, ${math(String.raw`0\le t\le 1`)} and ${math('\\ell')} is the piece length. A vertical load projects onto the local transverse axis with factor ${math(String.raw`\Delta X/L`)}. ${loadProjection} ${differentialRelations}`;
    section.append(description);
    section.insertAdjacentHTML('beforeend', math(String.raw`V(t)=V_0+Bt+Ct^2,\quad M(t)=M_0+\ell t(V_0+Bt/2+Ct^2/3)`,true));
    const midpoint = (q: string[]) => approximate(q[0])/2+approximate(q[1])/2;
    const curves: Record<Field,number[][]> = {V:[],M:[]};
    const rows: Record<Field,string[]> = {V:[],M:[]};
    const peak = {V:0,M:0};
    let physicalLength = 0, count = 0;
    for (const line of lines) {
        const [tag,...f] = line.split(' ');
        if (tag === 'P' && f.length === 10 && f.every(rational)) {
            const [a,b,B,C] = f, length=f.slice(4,6), v=f.slice(6,8), m=f.slice(8,10);
            physicalLength=midpoint(length);
            const left = approximate(a)*physicalLength, right = approximate(b)*physicalLength;
            const ell = (approximate(b)-approximate(a))*physicalLength;
            const linear=approximate(B), quadratic=approximate(C), v0=midpoint(v);
            curves.V.push([left,right,v0,linear,quadratic,0]);
            curves.M.push([left,right,midpoint(m),ell*v0,ell*linear/2,ell*quadratic/3]);
            const bCoefficient = exactLatex(B), cCoefficient = exactLatex(C);
            const enclosed = (name: string, limits: string[], unit: string) => {
                const relation = limits[0] === limits[1] ? '=' : '\\in';
                const value = limits[0] === limits[1] ? exactLatex(limits[0]) : bounds(limits).replaceAll('−', '-');
                return math(name + relation + quantity(value, unit));
            };
            const linearTerm = bCoefficient === '0' ? '' : `+(${quantity(bCoefficient, measureUnits.force)})`;
            const quadraticTerm = cCoefficient === '0' ? '' : `+(${quantity(cCoefficient, measureUnits.force)})`;
            const shear = math('V(t)=V_0' + (linearTerm && linearTerm + 't') + (quadraticTerm && quadraticTerm + 't^2'), true);
            const integral = 'V_0t' + (linearTerm && linearTerm + 't^2/2') + (quadraticTerm && quadraticTerm + 't^3/3');
            const moment = math(String.raw`M(t)=M_0+\ell[${integral}]`, true);
            section.insertAdjacentHTML('beforeend', `<div data-piece="${count++}" data-left="${a}" data-right="${b}" data-b="${B}" data-c="${C}" data-length-low="${length[0]}" data-length-high="${length[1]}" data-v-low="${v[0]}" data-v-high="${v[1]}" data-m-low="${m[0]}" data-m-high="${m[1]}"><h4>Member fraction ${math(exactLatex(a))} to ${math(exactLatex(b))}</h4><p>${enclosed('L', length, measureUnits.length)} and ${math(String.raw`\ell=(${exactLatex(b)}-${exactLatex(a)})L`)}. Substituting the signed vertical loads gives ${math('B=' + quantity(bCoefficient, measureUnits.force))} and ${math('C=' + quantity(cCoefficient, measureUnits.force))}. The starting values satisfy ${enclosed('V_0', v, measureUnits.force)} and ${enclosed('M_0', m, measureUnits.moment)}.</p>${shear}${moment}</div>`);
        } else if ((tag === 'V' || tag === 'M') && f.length === 10 && /^\d+$/.test(f[0]) && Number(f[0])<count &&
            ['start','end','interior','flat'].includes(f[1]) && f.slice(2,8).every(rational) && f.slice(8).every(x=>x==='0'||x==='1')) {
            const [piece,side,tLo,tHi,xLo,xHi,yLo,yHi,lo,hi]=f;
            peak[tag]=Math.max(peak[tag],Math.abs(approximate(yLo)),Math.abs(approximate(yHi)));
            const sideText = {start:'Right-hand limit',end:'Left-hand limit',flat:'Constant interval',interior:'Stationary point'}[side];
            rows[tag].push(`<tr data-candidate data-piece-index="${piece}" data-field="${tag}" data-side="${side}" data-t-low="${tLo}" data-t-high="${tHi}" data-x-low="${xLo}" data-x-high="${xHi}" data-y-low="${yLo}" data-y-high="${yHi}" data-min="${lo==='1'}" data-max="${hi==='1'}"><td>${sideText}</td><td>${bounds([tLo,tHi],side==='flat')}</td><td>${bounds([xLo,xHi])}</td><td>${bounds([yLo,yHi])}</td><td>${[lo==='1'?'Minimum':'',hi==='1'?'Maximum':''].filter(Boolean).join(' and ')||'—'}</td></tr>`);
        } else throw Error('Invalid record in the inclined diagram report.');
    }
    if (!count || !rows.V.length || !rows.M.length) throw Error('Incomplete inclined diagram.');
    for (const field of ['V','M'] as const) {
        section.insertAdjacentHTML('beforeend',`<h4>${field==='V'?'Shear force':'Bending moment'}</h4>`+
            drawPlot(field,physicalLength,peak[field]||1,curves[field])+
            `<p>The sketch uses midpoint coefficients. The table encloses the section values and every whole-member extremum. For a constant interval, the distance bounds enclose both ends. Interior candidates satisfy ${math(field==='V'?'q=0':'V=0')}.</p><table><thead><tr><th>Member side</th><th>Piece fraction ${math('t')}</th><th>${math('x')} (m)</th><th>${math(field)} (${unit[field]})</th><th>Whole-member extremum</th></tr></thead><tbody>${rows[field].join('')}</tbody></table>`);
    }
    return section;
}
