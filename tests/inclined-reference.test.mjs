/** Independent numerical references for Stage 1; these do not grant checked status. */
import test from 'node:test';
import assert from 'node:assert/strict';
import { analyse } from '../web/engine.ts';

const near = (actual, expected) => assert.ok(Math.abs(actual - expected) < 1e-8 * Math.max(1, Math.abs(expected)), `${actual} != ${expected}`);
function cantilever(reversed = false, loadPosition = 1) {
    return {
        nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 1, y: 2 }],
        members: [{ id: 'AB', a: reversed ? 'B' : 'A', b: reversed ? 'A' : 'B', EA: 2000000, EI: 20000 }],
        supports: [{ id: 'fixed', member: 'AB', t: reversed ? 1 : 0, kind: 'fixed', angle: 90 }],
        loads: [{ id: 'force', member: 'AB', kind: 'force', t: reversed ? 1 - loadPosition : loadPosition,
            end: 1, fx: 3, fy: -7, mz: 0, qEnd: 0 }],
    };
}

test('irrational-length cantilever agrees with axial and bending closed forms in either member direction', () => {
    const length = Math.sqrt(5), cosine = 1 / length, sine = 2 / length;
    const axialForce = cosine * 3 + sine * -7;
    const transverseForce = -sine * 3 + cosine * -7;
    const axialTip = axialForce * length / 2000000;
    const transverseTip = transverseForce * length ** 3 / (3 * 20000);
    for (const reversed of [false, true]) {
        const result = analyse(cantilever(reversed));
        assert.equal(result.status, 'stable');
        const tip = result.elements.flatMap(element => element.samples).find(sample => sample.x === 1 && sample.y === 2);
        assert.ok(tip);
        near(tip.ux, cosine * axialTip - sine * transverseTip);
        near(tip.uy, sine * axialTip + cosine * transverseTip);
        near(tip.rotation, transverseForce * length ** 2 / (2 * 20000));
        near(result.reactions[0].fx, -3);
        near(result.reactions[0].fy, 7);
        near(result.reactions[0].mz, 13);
    }
});

test('noncardinal roller and interior arbitrary force agree with independent global statics', () => {
    const model = cantilever(false, 0.4);
    model.supports[0].kind = 'pin';
    model.supports.push({ id: 'roller', member: 'AB', t: 1, kind: 'roller', angle: 37 });
    const result = analyse(model);
    assert.equal(result.status, 'stable');
    const cosine = Math.cos(37 * Math.PI / 180), sine = Math.sin(37 * Math.PI / 180);
    const magnitude = 0.4 * 13 / (sine - 2 * cosine);
    const atA = result.reactions.find(reaction => reaction.x === 0);
    const atB = result.reactions.find(reaction => reaction.x === 1);
    near(atB.fx, magnitude * cosine);
    near(atB.fy, magnitude * sine);
    near(atA.fx + atB.fx, -3);
    near(atA.fy + atB.fy, 7);
});

test('unrestrained inclined drawing remains a mechanism with and without applied load', () => {
    for (const loaded of [false, true]) {
        const model = cantilever();
        model.supports = [];
        if (!loaded) model.loads = [];
        assert.equal(analyse(model).status, 'unstable');
    }
});
