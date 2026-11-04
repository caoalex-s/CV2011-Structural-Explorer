/** Course SVG symbols and concise formula/substitution views for the first unit. */
import { forceSymbol, supportShape, symbolLabel, courseColors } from './symbols.js';
import { beamValues, lessonBeam } from './lesson-beam.js';
import type { BeamInputs, SupportCase } from './lesson-beam.js';
import { math } from './math.js';

const number = (value: number) => Number(value.toPrecision(5)).toString();
const label = (x: number, y: number, text: string, anchor = 'middle') =>
    `<text x="${x}" y="${y}" text-anchor="${anchor}" class="svg-label">${symbolLabel(text)}</text>`;
const support = (x: number, kind: string) =>
    `<g transform="translate(${x} 120)" class="support-stroke">${supportShape(kind)}</g>`;

export function beamDrawing(inputs: BeamInputs, section = 0.5, compression = false, supports: SupportCase = 'pin-roller', diagrams = true): string {
    const values = beamValues(inputs, section);
    const model = lessonBeam(inputs, supports);
    const leftX = 100, rightX = 660, loadX = leftX + 560 * inputs.position, cutX = leftX + 560 * section;
    const forceScale = 65 / inputs.load;
    const leftShearY = 285 - forceScale * values.left, rightShearY = 285 + forceScale * values.right;
    const momentBaseline = 450, momentHeight = 55;
    const momentY = momentBaseline + (compression ? -1 : 1) * momentHeight;
    // Force symbols share the insertion points used by the workspace. Labels
    // move into free space without moving arrows away from their lines of action.
    let drawing = `<title>Beam with downward force P at distance a from A</title>
        <path d="M${leftX} 120H${rightX}" class="beam-stroke"/>
        ${model.supports.map(item => support(leftX + 560 * item.t, item.kind)).join('')}
        ${label(leftX - 22, 113, 'A')}${label(rightX + 22, 113, 'B')}
        ${forceSymbol(loadX, 120, 0, -inputs.load, courseColors.force, `P = ${number(inputs.load)} kN`, 55)}
        <path d="M${leftX} 24V9H${leftX + 34}m-6-4 6 4-6 4M${leftX} 9l-4 6m4-6 4 6" class="axis-stroke"/>
        ${label(leftX + 46, 15, 'x')}${label(leftX - 11, 12, 'y')}
        <path d="M${leftX} 205H${rightX}M${leftX} 200V210M${rightX} 200V210M${loadX} 200V210" class="dimension-stroke"/>
        ${label((leftX + loadX) / 2, 198, `a = ${number(values.a)} m`)}
        ${label((leftX + rightX) / 2, 229, `L = ${number(inputs.span)} m`)}`;
    if (!diagrams) return drawing;
    drawing += `${forceSymbol(leftX, 120, 0, values.left, courseColors.reaction, '', 46, 30)}
        ${forceSymbol(rightX, 120, 0, values.right, courseColors.reaction, '', 46, 30)}
        ${label(leftX + 12, 180, `A_y = ${number(values.left)} kN`, 'start')}
        ${label(rightX - 12, 180, `B_y = ${number(values.right)} kN`, 'end')}
        <path d="M${leftX} 285H${rightX}M${leftX} ${momentBaseline}H${rightX}" class="axis-stroke"/>
        <path d="M${leftX} 285V${leftShearY}H${loadX}V${rightShearY}H${rightX}V285Z" class="shear-fill"/>
        <path d="M${leftX} ${momentBaseline}L${loadX} ${momentY}L${rightX} ${momentBaseline}Z" class="moment-fill"/>
        ${label(48, 289, 'V (kN)')}${label(48, momentBaseline + 4, 'M (kN m)')}
        ${label((leftX + loadX) / 2, leftShearY - 8, `+${number(values.left)}`)}
        ${label((loadX + rightX) / 2, rightShearY + 19, `−${number(values.right)}`)}
        ${label(loadX, momentY + (compression ? -12 : 21), `M = ${number(values.peak)} kN m`)}
        <path d="M${cutX} 249V535" class="section-line"/>
        <circle cx="${cutX}" cy="${285 - forceScale * values.shear}" r="4" class="section-dot"/>
        <circle cx="${cutX}" cy="${momentBaseline + (compression ? -1 : 1) * momentHeight * values.moment / values.peak}" r="4" class="section-dot"/>
        <rect x="${loadX - 22}" y="30" width="44" height="98" fill="transparent" class="load-handle" data-drag-load="true"><title>Drag the force horizontally, or use the load-position slider</title></rect>`;
    return drawing;
}

/** Substitution follows each generic equation and keeps rounded outputs explicit. */
export function reactionEquations(inputs: BeamInputs): string {
    const { load: P, span: L } = inputs;
    const { a, left, right } = beamValues(inputs);
    return math(String.raw`\begin{aligned} B_y&=\frac{Pa}{L}=\frac{${P}(${number(a)})}{${L}}\approx ${number(right)}\;\mathrm{kN},\\ A_y&=\frac{P(L-a)}{L}=\frac{${P}(${L}-${number(a)})}{${L}}\approx ${number(left)}\;\mathrm{kN}.\end{aligned}`, true);
}

export function sectionEquations(inputs: BeamInputs, section: number): string {
    const { load: P, span: L, position } = inputs;
    const { a, x, left, shear, moment, peak } = beamValues(inputs, section);
    const after = section >= position;
    const shearRule = after ? 'A_y-P' : 'A_y';
    const momentRule = after ? 'A_y x-P(x-a)' : 'A_y x';
    const shearNumbers = after ? `${number(left)}-${P}` : number(left);
    const momentNumbers = `${number(left)}(${number(x)})${after ? `-${P}(${number(x)}-${number(a)})` : ''}`;
    return `<div class="section-readout">${math(`x=${number(x)}\\;\\mathrm{m}`, true)}
        ${math(`N=0,\\quad V=${shearRule}=${shearNumbers}\\approx ${number(shear)}\\;\\mathrm{kN}.`, true)}
        ${math(`M=${momentRule}=${momentNumbers}\\approx ${number(moment)}\\;\\mathrm{kN}\\,\\mathrm{m}.`, true)}</div>
        <div class="peak-readout">${math(String.raw`M_{\max}=\frac{Pa(L-a)}{L}=\frac{${P}(${number(a)})(${L}-${number(a)})}{${L}}\approx ${number(peak)}\;\mathrm{kN}\,\mathrm{m}.`, true)}</div>`;
}
