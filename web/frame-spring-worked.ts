import { endConnection, referenceMember, type Model } from './engine.js';
import { binary64 } from './frame-rational.js';
import type { decodeInclinedReleaseReport } from './frame-inclined-release-result.js';
import type { IntervalReadout } from './frame-interval-result.js';
import { memberLabel } from './model-view.js';
import { math, measureUnits, quantity } from './math.js';
import { roundedDecimal } from './portal-candidate.js';

/** Use exact checker endpoints for the evidence and rounded midpoints for the displayed substitution. */
function value(name: string, interval: IntervalReadout, expression: string, display = false): HTMLSpanElement {
    const span = document.createElement('span');
    span.dataset.springValue = name;
    span.dataset.lower = interval.lower.numerator + '/' + interval.lower.denominator;
    span.dataset.upper = interval.upper.numerator + '/' + interval.upper.denominator;
    span.innerHTML = math(expression, display);
    return span;
}

export function springExplanation(model: Model, report: ReturnType<typeof decodeInclinedReleaseReport>): HTMLElement[] {
    const result: HTMLElement[] = [];
    const sides = model.members.flatMap(member => (['a', 'b'] as const).map(end => ({ member, end })));
    const expected = sides.filter(({ member, end }) => typeof endConnection(model, member, end).rotation === 'number');
    if (expected.length !== report.springs.length) throw Error('Spring count differs from the drawing.');
    for (const spring of report.springs) {
        const { member, end } = sides[spring.side];
        const node = member[end];
        const reference = referenceMember(model, node);
        const endFace = report.faces.find(face => face.member === member.id && face.node === node);
        const refFace = report.faces.find(face => face.member === reference && face.node === node);
        const k = endConnection(model, member, end).rotation;
        if (!refFace || !endFace || typeof k !== 'number') throw Error('Spring attachment differs from the drawing.');
        const exact = binary64(k);
        if (String(exact.n) !== spring.stiffness.numerator || String(exact.d) !== spring.stiffness.denominator)
            throw Error('Spring stiffness differs from the drawing.');
        const box = document.createElement('section');
        box.dataset.springSide = String(spring.side);
        const title = document.createElement('h4');
        title.textContent = 'Rotational spring between ' + memberLabel(model, model.members.find(m => m.id === reference)!) +
            ' (reference) and ' + memberLabel(model, member) + ' (connected end)';
        const law = document.createElement('p');
        law.innerHTML = `Take counterclockwise rotation as positive. The relative rotation is ${math(String.raw`\Delta\theta=\theta_{\mathrm{end}}-\theta_{\mathrm{ref}}`)}. The spring transmits ${math(String.raw`T=k_\theta\Delta\theta`)}. It exerts ${math('+T')} on the reference and ${math('-T')} on the connected end.`;
        const radians = (interval: IntervalReadout) => quantity(roundedDecimal(interval.midpoint, 8), '\\mathrm{rad}');
        const moment = (interval: IntervalReadout) => quantity(roundedDecimal(interval.midpoint, 8), measureUnits.moment);
        const substitution = document.createElement('p');
        substitution.append('The checked rotations are ',
            value('end-rotation', endFace.rotation, String.raw`\theta_{\mathrm{end}}\approx ${radians(endFace.rotation)}`), ' and ',
            value('reference-rotation', refFace.rotation, String.raw`\theta_{\mathrm{ref}}\approx ${radians(refFace.rotation)}`), '.');
        substitution.append(
            value('relative-rotation', spring.relativeRotation, String.raw`\begin{aligned}
                \Delta\theta&\approx (${radians(endFace.rotation)})-(${radians(refFace.rotation)})\\
                &\approx ${radians(spring.relativeRotation)}
                \end{aligned}`, true),
            value('transmitted-moment', spring.transmittedMoment, String.raw`\begin{aligned}
                T&\approx (${quantity(String(k), '\\mathrm{kN}\\,\\mathrm{m}/\\mathrm{rad}')})(${radians(spring.relativeRotation)})\\
                &\approx ${moment(spring.transmittedMoment)}
                \end{aligned}`, true));
        const action = spring.transmittedMoment.midpoint;
        const opposite = { numerator: String(-BigInt(action.numerator)), denominator: action.denominator };
        substitution.insertAdjacentHTML('beforeend', ` The spring couples are approximately ${math(moment(spring.transmittedMoment))} on the reference and ${math(quantity(roundedDecimal(opposite, 8), measureUnits.moment))} on the connected end.`);
        const balance = document.createElement('p');
        balance.innerHTML = `For the connected end, let ${math('C')} be the sum of externally applied and support couples there, counterclockwise positive.
            At local ${math(end === 'a' ? 'x=0' : 'x=L')}, the section moment in the local sign convention is ${math(end === 'a' ? 'M=T-C' : 'M=C-T')}.
            The checked section moment on this face is approximately ${math(moment(endFace.moment))}.`;
        box.append(title, law, substitution, balance);
        result.push(box);
    }
    return result;
}
