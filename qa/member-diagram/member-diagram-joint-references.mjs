/** Hand references for comparing rigid, hinged and spring diagrams on the
 * same beam. A–B and B–C are drawn from left to right, each 4 m long.
 * A and C are fixed. EI = 20 000 kN m². A spring uses AB as the reference end.
 * Each member uses its own distance x from its first drawn end.
 */

const span = 4;
const modes = ['rigid', 'hinge', 'spring5000', 'spring2500'];

function endpoint(field, side, x, value, minimum, maximum) {
    return { field, side, index: 0, x, value, minimum, maximum };
}

function linearDiagram(shear, startMoment) {
    const endMoment = startMoment + span * shear;
    return {
        pieces: [{ start: 0, end: span, shear: [shear], moment: [startMoment, shear] }],
        candidates: [
            endpoint('V', 'start', 0, shear, true, true),
            endpoint('V', 'flat', [0, span], shear, true, true),
            endpoint('V', 'end', span, shear, true, true),
            endpoint('M', 'start', 0, startMoment, shear > 0, shear < 0),
            endpoint('M', 'end', span, endMoment, shear < 0, shear > 0),
        ],
    };
}

// With P=10 kN down at B and no applied joint couple, the shears are ±5 kN.
// Integrating EI v″=M on AB gives thetaRef = -1/500 + T/5000 rad.
// Reflection gives thetaConnected = -thetaRef. The spring imposes
// T = k(thetaConnected - thetaRef). For a hinge T=0. For a rigid joint the
// angle difference vanishes.
const pointTransmission = [10, 0, 20 / 3, 5];
export const nodalLoad = Object.fromEntries(modes.map((mode, index) => {
    const transmission = pointTransmission[index];
    const referenceRotation = -1 / 500 + transmission / 5000;
    return [mode, {
        AB: linearDiagram(5, transmission - 20),
        BC: linearDiagram(-5, transmission),
        referenceRotation,
        connectedRotation: -referenceRotation,
        rotationJump: -2 * referenceRotation,
        transmission,
    }];
}));

// For w=4−2x kN/m downward on AB and an unloaded BC, moment continuity
// gives M_AB=T−4R+32/3+Rx−2x²+x³/3 and M_BC=T+Rx, where R=V_AB(0).
// Integrating from the fixed supports gives EI v_B on the left as
// 8T−64R/3+896/15 and on the right as 8T+64R/3. Matching these gives R=7/5.
// The CCW rotation jump is (−8T−64/3)/EI. Use the same joint laws as above.
const affineTransmission = [-8 / 3, 0, -16 / 9, -4 / 3];
const offset = Math.sqrt(13 / 5);
const ordinateOffset = 2 * offset ** 3 / 3;
export const distributedLoad = Object.fromEntries(modes.map((mode, index) => {
    const transmission = affineTransmission[index];
    const startMoment = transmission + 76 / 15;
    const centralMoment = transmission + 38 / 15;
    const referenceRotation = (4 * transmission - 56 / 5 + 64 / 3) / 20000;
    const connectedRotation = (-4 * transmission - 56 / 5) / 20000;
    return [mode, {
        AB: {
            pieces: [{ start: 0, end: span, shear: [7 / 5, -4, 1], moment: [startMoment, 7 / 5, -2, 1 / 3] }],
            candidates: [
                endpoint('V', 'start', 0, 7 / 5, false, true),
                endpoint('V', 'end', span, 7 / 5, false, true),
                endpoint('V', 'interior', 2, -13 / 5, true, false),
                endpoint('M', 'start', 0, startMoment, false, false),
                endpoint('M', 'end', span, transmission, false, false),
                endpoint('M', 'interior', 2 - offset, centralMoment + ordinateOffset, false, true),
                endpoint('M', 'interior', 2 + offset, centralMoment - ordinateOffset, true, false),
            ],
        },
        BC: linearDiagram(7 / 5, transmission),
        referenceRotation,
        connectedRotation,
        rotationJump: connectedRotation - referenceRotation,
        transmission,
    }];
}));
