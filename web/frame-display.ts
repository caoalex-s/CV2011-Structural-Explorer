/** Named display values come exclusively from the accepted packet decoder. */
import type { CheckedFrameValues } from './frame-result.js';
import { roundedDecimal } from './portal-candidate.js';

export function frameDescriptions(frame: CheckedFrameValues): string[] {
    const exactParameter = (value: { numerator: string; denominator: string }) =>
        value.denominator === '1' ? value.numerator : `${value.numerator}/${value.denominator}`;
    const descriptions: string[] = [];
    if (frame.kind === 'solution') {
        const [normal, shear, moment, rotation, ux, uy] = frame.readouts;
        descriptions.push(`Member ${frame.query.member}, t = ${exactParameter(frame.query.parameter)}, ${frame.query.cutSide} limit`,
            `Axial force N: ${roundedDecimal(normal, 3)} kN. Shear force V: ${roundedDecimal(shear, 3)} kN. Bending moment M: ${roundedDecimal(moment, 3)} kN m.`,
            `Section displacement: ux ${roundedDecimal(ux, 3, 1000n)} mm, uy ${roundedDecimal(uy, 3, 1000n)} mm. Rotation: ${roundedDecimal(rotation, 6)} rad.`);
    } else descriptions.push('The entries below describe one nonzero mechanism motion with arbitrary scale.');
    for (const point of frame.points) {
        const label = point.owner === 'node' ? `Node ${point.id}` : `Member ${point.id} at t = ${exactParameter(point.parameter)}`;
        if (frame.kind === 'solution') {
            descriptions.push(`${label}: ux ${roundedDecimal(point.motion[0], 3, 1000n)} mm, uy ${roundedDecimal(point.motion[1], 3, 1000n)} mm, rotation ${roundedDecimal(point.motion[2], 6)} rad.`);
            if (point.reaction) descriptions.push(`${label}, grouped reaction: Fx ${roundedDecimal(point.reaction[0], 3)} kN, Fy ${roundedDecimal(point.reaction[1], 3)} kN, Mz ${roundedDecimal(point.reaction[2], 3)} kN m.`);
        } else descriptions.push(`${label}: zx ${roundedDecimal(point.motion[0], 6)}, zy ${roundedDecimal(point.motion[1], 6)}, zrotation ${roundedDecimal(point.motion[2], 6)}.`);
    }
    descriptions.push('Displayed decimals are rounded. The local export retains the exact values and their point identities.');
    return descriptions;
}

export function frameStatus(frame: CheckedFrameValues): string {
    if (frame.kind === 'solution') return 'Accepted by the compiled proved checker: unique linear equilibrium.';
    return frame.loadWork.numerator === '0'
        ? 'Checked mechanism. This witness does not determine load compatibility.'
        : 'Checked mechanism. Applied loads are incompatible with equilibrium.';
}
