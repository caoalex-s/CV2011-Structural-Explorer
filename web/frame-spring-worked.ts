import { endConnection, referenceMember, type Model } from './engine.js';
import { binary64 } from './frame-rational.js';
import type { decodeInclinedReleaseReport } from './frame-inclined-release-result.js';
import type { IntervalReadout } from './frame-interval-result.js';
import { memberLabel } from './model-view.js';
import { roundedDecimal } from './portal-candidate.js';

/** Use exact checker endpoints for the evidence and rounded midpoints for the displayed substitution. */
function value(name: string, interval: IntervalReadout): HTMLSpanElement {
    const span = document.createElement('span');
    span.dataset.springValue = name;
    span.dataset.lower = interval.lower.numerator + '/' + interval.lower.denominator;
    span.dataset.upper = interval.upper.numerator + '/' + interval.upper.denominator;
    span.textContent = roundedDecimal(interval.midpoint, 8);
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
        law.textContent = 'Take counterclockwise rotation as positive. The relative rotation is Δθ = θend − θref. The spring transmits T = kθ Δθ. It exerts +T on the reference and −T on the connected end.';
        const substitution = document.createElement('p');
        substitution.append('Δθ ≈ (', value('end-rotation', endFace.rotation), ' − (', value('reference-rotation', refFace.rotation),
            ')) rad ≈ ', value('relative-rotation', spring.relativeRotation), ' rad. T ≈ (', String(k), ' kN m/rad) × (',
            roundedDecimal(spring.relativeRotation.midpoint, 8), ' rad) ≈ ', value('transmitted-moment', spring.transmittedMoment), ' kN m.');
        const action = spring.transmittedMoment.midpoint;
        const opposite = { numerator: String(-BigInt(action.numerator)), denominator: action.denominator };
        substitution.append(' The spring couples are approximately ', roundedDecimal(action, 8),
            ' kN m on the reference and ', roundedDecimal(opposite, 8), ' kN m on the connected end.');
        const balance = document.createElement('p');
        balance.textContent = 'For the connected end, let C be the sum of externally applied and support couples there, counterclockwise positive. ' +
            (end === 'a' ? 'At local x = 0, the section moment in the local sign convention is M = T − C.' :
                'At local x = L, the section moment in the local sign convention is M = C − T.') +
            ' The checked section moment on this face is approximately ' + roundedDecimal(endFace.moment.midpoint, 8) + ' kN m.';
        box.append(title, law, substitution, balance);
        result.push(box);
    }
    return result;
}
