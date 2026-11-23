/** Independent static equilibrium benchmark for a pin and vertical roller.
 * Coordinates are metres from the left support. Forces are in kN and positive
 * y is upwards. force is the signed magnitude applied downwards at loadAt.
 */
import assert from 'node:assert/strict';

export function pointLoadReference({ span = 8, force = 20, loadAt = 4, cut = loadAt, limit = 'left' } = {}) {
    assert.ok([span, force, loadAt, cut].every(Number.isFinite));
    assert.ok(0 < loadAt && loadAt < span && 0 <= cut && cut <= span);
    assert.ok(['left', 'right'].includes(limit));

    // Take whole-beam moments about the supports separately.
    const rightReaction = force * loadAt / span;
    const leftReaction = force * (span - loadAt) / span;
    const loadOnLeft = cut > loadAt || (cut === loadAt && limit === 'right');
    const loadAction = { name: 'P', x: loadAt, vertical: -force };
    const leftActions = [{ name: 'Ay', x: 0, vertical: leftReaction }];
    const rightActions = [{ name: 'By', x: span, vertical: rightReaction }];
    (loadOnLeft ? leftActions : rightActions).push(loadAction);

    const verticalBalance = actions => actions.reduce((total, action) => total + action.vertical, 0);
    const momentBalance = actions => actions.reduce(
        (total, action) => total + (action.x - cut) * action.vertical, 0
    );
    const cleanZero = value => value === 0 ? 0 : value;
    // For a positive V, the internal shear acts downwards on the retained left
    // body and upwards on the retained right body. Positive M is sagging.
    const left = { N: 0, V: cleanZero(verticalBalance(leftActions)), M: cleanZero(-momentBalance(leftActions)) };
    const right = { N: 0, V: cleanZero(-verticalBalance(rightActions)), M: cleanZero(momentBalance(rightActions)) };
    for (const result of ['N','V','M']) {
        assert.ok(Math.abs(left[result] - right[result]) <= 1e-9 * Math.max(1, Math.abs(left[result])));
    }
    return {
        span, force, loadAt, cut, limit, relevantLimit: cut === loadAt,
        reactions: { Ax: 0, Ay: cleanZero(leftReaction), By: cleanZero(rightReaction) },
        actions: { left: leftActions, right: rightActions }, forces: left,
        cutActions: {
            left: { vertical: cleanZero(-left.V), counterclockwise: left.M },
            right: { vertical: left.V, counterclockwise: cleanZero(-left.M) }
        }
    };
}
