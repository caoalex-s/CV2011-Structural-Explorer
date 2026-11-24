import test from 'node:test';
import assert from 'node:assert/strict';
import { analyse, angleVector, example } from '../web/engine.ts';
import { createEvidenceEnvelope, parseDrawing, parseEvidenceModel } from '../web/model-evidence.ts';

const near = (value, expected) => assert.ok(Math.abs(value - expected) < 1e-7, `${value} differs from ${expected}`);
const query = {member:'AB', parameter:0.5, cutSide:'right', quantity:'M', units:'kN m', signConvention:'sagging positive'};

test('signed line loading per metre on inclined and reversed cantilevers', async () => {
    for (const reverse of [false, true]) for (const direction of [0, 37, 90, 'member-normal', undefined]) {
        const model = example('cantilever');
        model.nodes[1].x = reverse ? -3 : 3;
        model.nodes[1].y = reverse ? -4 : 4;
        const c = model.nodes[1].x / 5, s = model.nodes[1].y / 5;
        Object.assign(model.loads[0], {kind:'distributed', t:0, end:1, fy:-2, qEnd:4, mz:0});
        if (direction !== undefined) model.loads[0].direction = direction;
        const axis = direction === 'member-normal' ? {x:-s, y:c} : angleVector(direction ?? 90);
        const axial = c*axis.x+s*axis.y, transverse = -s*axis.x+c*axis.y;
        const analysis = analyse(model);
        assert.equal(analysis.status,'stable');
        const reaction = analysis.reactions[0];
        near(reaction.fx,-5*axis.x); near(reaction.fy,-5*axis.y); near(reaction.mz,-25*transverse);
        const mid = analysis.elements[0].samples[20];
        near(mid.N,6.25*axial); near(mid.V,-6.25*transverse); near(mid.M,9.375*transverse);
    }
});

test('direction survives file round-trip and binds the mechanical source', async () => {
    const model = example('frame');
    const load = model.loads[0];
    const section = {...query,member:load.member};
    const hashes = new Set();
    for (const axis of [undefined,0,37,'member-normal']) {
        if (axis !== undefined) load.direction = axis;
        const file = JSON.stringify({version:axis === undefined ? 2 : 3,model});
        assert.deepEqual(parseDrawing(JSON.parse(file)).loads[0], load);
        const envelope = await createEvidenceEnvelope(model,section,file);
        hashes.add(envelope.bindings.mechanical);
        if (axis !== undefined) assert.throws(()=>parseEvidenceModel(model),/compiled checker/);
    }
    assert.equal(hashes.size,4);
    load.direction = 'unknown';
    assert.throws(()=>parseDrawing(model));
    assert.equal(analyse(model).status,'invalid');
});
