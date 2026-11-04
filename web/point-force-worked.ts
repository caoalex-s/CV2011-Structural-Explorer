/** Closed-form elastic response for the endpoint-supported point-force beam.
 * P is signed downward, x and a are measured from the left end, and EI is
 * constant in kN m². Slope is counterclockwise-positive; v is upward-positive.
 */
import type { Model } from './engine.js';
import { pointForceRules } from './point-force-rules.js';

export function pointForceWorked(model: Model, section: number) {
    const rule = pointForceRules(model, section);
    const EI = model.members[0]?.EI;
    if (!rule || !Number.isFinite(EI) || EI <= 0) return null;
    const { P, L, a, x, leftReaction, after } = rule;
    const thetaLeft = -P * (L - a) * (L * L - (L - a) ** 2) / (6 * L * EI);
    const distance = after ? x - a : 0;
    const theta = thetaLeft + (leftReaction * x ** 2 - P * distance ** 2) / (2 * EI);
    const displacement = thetaLeft * x + (leftReaction * x ** 3 - P * distance ** 3) / (6 * EI);
    return { ...rule, EI, thetaLeft, theta, displacement };
}
