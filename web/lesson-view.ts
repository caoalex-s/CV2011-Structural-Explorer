/** Course SVG symbols and concise formula/substitution views for the first unit. */
import { forceSymbol, momentSymbol, supportShape, symbolLabel, courseColors } from './symbols.js';
import { beamValues, lessonBeam } from './lesson-beam.js';
import type { BeamInputs, SupportCase } from './lesson-beam.js';
import { math } from './math.js';

const number = (value: number) => Number(value.toPrecision(5)).toString();
function label(x: number, y: number, text: string, anchor = 'middle'): string {
    // Here a is the load coordinate. Keep the shared prose-aware formatter from
    // treating every standalone English article "a" as a mathematical variable.
    const notation = symbolLabel(text).replace(/(?<![A-Za-z0-9])a(?![A-Za-z0-9])/g,
        '<tspan class="svg-variable">a</tspan>');
    return `<text x="${x}" y="${y}" text-anchor="${anchor}" class="svg-label">${notation}</text>`;
}
const support = (x: number, kind: string) =>
    `<g transform="translate(${x} 120)" class="support-stroke">${supportShape(kind)}</g>`;

export type DiagramScale = 'constant' | 'automatic';

export function beamDrawing(inputs: BeamInputs, section = 0.5, compression = false, supports: SupportCase = 'pin-roller', diagrams: boolean | 'reactions' = true, scale: DiagramScale = 'constant'): string {
    const values = beamValues(inputs, section);
    const model = lessonBeam(inputs, supports);
    const leftX = 100, rightX = 660, loadX = leftX + 560 * inputs.position, cutX = leftX + 560 * section;
    // Constant scales fit the entire allowed input range: |V| <= 45 kN,
    // M_max <= 150 kN m. Automatic scales remain useful for small responses.
    const forceScale = scale === 'automatic' ? 65 / inputs.load : 1.3;
    const leftShearY = 285 - forceScale * values.left, rightShearY = 285 + forceScale * values.right;
    const momentBaseline = 450, momentHeight = scale === 'automatic' ? 55 : values.peak * 0.5;
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
        ${label(rightX - 12, 180, `B_y = ${number(values.right)} kN`, 'end')}`;
    const handle = `<rect x="${loadX - 22}" y="30" width="44" height="98" fill="transparent" class="load-handle" data-drag-load="true"><title>Drag the force horizontally, or use the load-position slider</title></rect>`;
    if (diagrams === 'reactions') return drawing + handle;
    drawing += `<path d="M${leftX} 285H${rightX}M${leftX} ${momentBaseline}H${rightX}" class="axis-stroke"/>
        <path d="M${leftX} 285V${leftShearY}H${loadX}V${rightShearY}H${rightX}V285Z" class="shear-fill"/>
        <path d="M${leftX} ${momentBaseline}L${loadX} ${momentY}L${rightX} ${momentBaseline}Z" class="moment-fill"/>
        ${label(48, 289, 'V (kN)')}${label(48, momentBaseline + 4, 'M (kN m)')}
        ${label((leftX + loadX) / 2, leftShearY - 8, `+${number(values.left)}`)}
        ${label((loadX + rightX) / 2, rightShearY + 19, `−${number(values.right)}`)}
        ${label(loadX, momentY + (compression ? -12 : 21), `M = ${number(values.peak)} kN m`)}
        <path d="M${cutX} 249V535" class="section-line"/>
        <circle cx="${cutX}" cy="${285 - forceScale * values.shear}" r="4" class="section-dot"/>
        <circle cx="${cutX}" cy="${momentBaseline + (compression ? -1 : 1) * momentHeight * values.moment / values.peak}" r="4" class="section-dot"/>
        ${handle}`;
    return drawing;
}

/** The retained free body uses the same section and one-sided rule as the readout.
 * Geometry is fitted to the retained length; action points remain exact.
 * Cut actions are assumed positive, even when their calculated values are negative.
 */
export function cutDrawing(inputs: BeamInputs, section: number): string {
    const { a, x } = beamValues(inputs, section);
    const includesLoad = section >= inputs.position;
    const atLoad = Math.abs(section - inputs.position) < 1e-9;
    const leftX = 100, cutX = 620, beamY = 100;
    const loadX = leftX + (cutX - leftX) * a / x;
    const condition = atLoad ? 'x = a (right-hand cut)' : includesLoad ? 'x > a' : 'x < a';
    return `<title>Retained left free body: ${condition}. Positive cut actions are assumed.</title>
        <path d="M${leftX} ${beamY}H${cutX}" class="beam-stroke"/>
        ${forceSymbol(leftX, beamY, 0, 1, courseColors.reaction, '', 48, 0)}
        ${label(leftX - 18, 143, 'A_y', 'end')}${label(leftX, 86, 'A')}
        ${includesLoad ? `<g data-cut-load="P">${forceSymbol(loadX, beamY, 0, -1, courseColors.force, '', 48, 0)}${label(loadX - 12, 45, 'P', 'end')}</g>` : ''}
        <path d="M${cutX} 40V168" class="section-line"/>
        <g data-cut-action="N" data-origin-x="${cutX}" data-origin-y="${beamY}"><path d="M${cutX} ${beamY}h90m-9-5 9 5-9 5" class="load-stroke"/></g>
        <g data-cut-action="V" data-origin-x="${cutX}" data-origin-y="${beamY}"><path d="M${cutX} ${beamY}v65m-5-9 5 9 5-9" class="load-stroke"/></g>
        ${momentSymbol(cutX, beamY, 1, courseColors.force, '', 30)}
        ${label(cutX + 102, 105, 'N')}${label(cutX + 17, 169, 'V')}${label(cutX + 42, 58, 'M')}
        <path d="M${leftX} 197H${cutX}M${leftX} 192V202M${cutX} 192V202" class="dimension-stroke"/>
        ${label((leftX + cutX) / 2, 220, `x = ${number(x)} m`)}
        ${includesLoad ? `<path d="M${loadX} 178H${cutX}M${loadX} 173V183M${cutX} 173V183" class="dimension-stroke"/>${label((loadX + cutX) / 2, 192, `x − a = ${number(x - a)} m`)}` : ''}
        ${label(100, 24, condition, 'start')}`;
}

/** Equilibrium precedes substitution, with the same retained loads as the figure. */
export function cutEquations(inputs: BeamInputs, section: number): string {
    const after = section >= inputs.position;
    return math(String.raw`\begin{aligned}
        \sum F_x=0:&\quad N=0,\\
        \sum F_y=0:&\quad A_y${after ? '-P' : ''}-V=0,\\
        \sum M_{\mathrm{cut}}=0:&\quad M-A_yx${after ? '+P(x-a)' : ''}=0.
        \end{aligned}`, true);
}

/** Readable values beside the full-span overview, including on a phone. */
export function diagramReadout(inputs: BeamInputs, section: number): string {
    const { x, shear, moment, peak } = beamValues(inputs, section);
    return [String.raw`x=${number(x)}\;\mathrm m`,
        String.raw`V=${number(shear)}\;\mathrm{kN}`,
        String.raw`M=${number(moment)}\;\mathrm{kN}\,\mathrm m`,
        String.raw`M_{\max}=${number(peak)}\;\mathrm{kN}\,\mathrm m`]
        .map(expression => `<span>${math(expression)}</span>`).join('');
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
