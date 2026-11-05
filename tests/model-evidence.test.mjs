import test from 'node:test';
import assert from 'node:assert/strict';
import { example, referenceMember } from '../web/engine.ts';
import { createEvidenceEnvelope, EvidenceRequests, parseEvidenceModel } from '../web/model-evidence.ts';

const query = { member: 'AB', parameter: 0.5, cutSide: 'left', quantity: 'M', units: 'kN m', signConvention: 'sagging positive' };
const snapshot = () => example('beam');

test('strict versioned parser accepts local and exported shapes with explicit defaults', () => {
    const model = snapshot();
    const local = parseEvidenceModel(model);
    assert.deepEqual(parseEvidenceModel({ version: 2, model }), local);
    assert.equal(local.nodes[0].joint, 'rigid');
    assert.equal(local.supports[0].fixX, false);
    assert.throws(() => parseEvidenceModel({ version: 3, model }), /version-2/);
    assert.throws(() => parseEvidenceModel({ version: 2, model, extra: true }), /unknown field/);
    for (const edit of [
        m => { m.nodes[0].x = NaN; },
        m => { m.members[0].EI = 0; },
        m => { m.members[0].a = 'missing'; },
        m => { m.members[0].connectionA = { axial: 'free', transverse: 0, rotation: 'rigid' }; },
        m => { m.nodes[0].referenceMember = 'missing'; },
        m => { m.loads[0].kind = 'other'; },
        m => { m.loads[0].t = 2; },
        m => { m.supports[0].fixX = 'true'; },
        m => { m.supports.push({ ...m.supports[0] }); },
        m => { m.loads[0].unexpected = 1; },
    ]) {
        const invalid = snapshot(); edit(invalid);
        assert.throws(() => parseEvidenceModel(invalid));
    }
    const spring = example('semi-rigid');
    delete spring.nodes[1].rotationStiffness;
    assert.equal(parseEvidenceModel(spring).nodes[1].rotationStiffness, 20000);
});

test('mechanical order and requested reference are retained rather than sorted', async () => {
    const model = example('hinge');
    const before = await createEvidenceEnvelope(model, query);
    assert.equal(referenceMember(before.model, 'B'), 'AB');
    const reordered = structuredClone(model); reordered.members.reverse();
    const after = await createEvidenceEnvelope(reordered, query);
    assert.equal(referenceMember(after.model, 'B'), 'BC');
    assert.notEqual(before.bindings.mechanical, after.bindings.mechanical);
    model.nodes[1].referenceMember = 'BC';
    const requested = await createEvidenceEnvelope(model, query);
    assert.equal(requested.model.nodes[1].referenceMember, 'BC');
    assert.notEqual(before.bindings.mechanical, requested.bindings.mechanical);
});

test('binding partitions, raw source and immutable binary64 snapshot', async () => {
    const model = snapshot();
    const source = JSON.stringify({ version: 2, model });
    const first = await createEvidenceEnvelope(model, query, source);
    const renamed = structuredClone(model); renamed.loads[0].label = 'F_A';
    const second = await createEvidenceEnvelope(renamed, query);
    assert.equal(first.bindings.mechanical, second.bindings.mechanical);
    assert.notEqual(first.bindings.display, second.bindings.display);
    assert.equal(first.bindings.query, second.bindings.query);
    assert.match(first.bindings.rawSource, /^[0-9a-f]{64}$/);
    assert.equal(first.bindings.exactAdapter, null);
    assert.equal(first.status, 'pending-not-formally-verified');
    assert.match(first.numericSemantics, /binary64/);
    assert.ok(Object.isFrozen(first.model.loads[0]));
    model.loads[0].fy = 999;
    assert.notEqual(first.model.loads[0].fy, 999);
    await assert.rejects(createEvidenceEnvelope(model, query, source), /does not match/);
    const queryEdit = await createEvidenceEnvelope(renamed, { ...query, cutSide: 'right' });
    assert.notEqual(second.bindings.query, queryEdit.bindings.query);
});

test('requests reject out-of-order and mechanically or query-stale results', () => {
    const model = snapshot(), requests = new EvidenceRequests();
    requests.update(model, query);
    const older = requests.begin(), newer = requests.begin();
    assert.throws(() => requests.accept(older, 'old'), /Stale/);
    assert.equal(requests.accept(newer, 'new'), 'new');
    model.loads[0].label = 'F_A'; requests.update(model, query);
    assert.equal(requests.accept(newer, 'still current'), 'still current');
    model.loads[0].fy -= 1; requests.update(model, query);
    model.loads[0].fy += 1; requests.update(model, query);
    assert.throws(() => requests.accept(newer, 'reverted'), /Stale/);
    const next = requests.begin(); requests.update(model, { ...query, parameter: 0.6 });
    assert.throws(() => requests.accept(next, 'wrong section'), /Stale/);
});


test('distinct source lexemes can bind the same binary64 mechanics', async () => {
    const model = snapshot(); model.nodes[0].x = 0.1;
    const source = JSON.stringify({ version: 2, model });
    const alternate = source.replace('"x":0.1', '"x":0.10000000000000001');
    const first = await createEvidenceEnvelope(JSON.parse(source), query, source);
    const second = await createEvidenceEnvelope(JSON.parse(alternate), query, alternate);
    assert.equal(first.bindings.mechanical, second.bindings.mechanical);
    assert.notEqual(first.bindings.rawSource, second.bindings.rawSource);
});
