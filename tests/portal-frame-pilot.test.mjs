import test from 'node:test';
import assert from 'node:assert/strict';
import { buildPortalPilot, validatePortalTopology } from '../scripts/portal-frame-pilot.mjs';
const { verifyExactCutArtifact } = await import('../web/exact-cut-adapter.ts');

test('pilot uses the unchanged shipped portal, including downward CD and both fixed bases', async () => {
    const { trace, envelope, artifact, leanSource } = await buildPortalPilot();
    const original = trace.identity.unchangedOriginalModel;
    assert.deepEqual(original.nodes, [
        { id: 'A', x: 0, y: 0 }, { id: 'B', x: 0, y: 4 },
        { id: 'C', x: 6, y: 4 }, { id: 'D', x: 6, y: 0 },
    ]);
    assert.deepEqual(original.members, [
        { id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 },
        { id: 'BC', a: 'B', b: 'C', EA: 2000000, EI: 20000 },
        { id: 'CD', a: 'C', b: 'D', EA: 2000000, EI: 20000 },
    ]);
    assert.deepEqual(original.supports, [
        { id: 'S1', member: 'AB', t: 0, kind: 'fixed', angle: 90 },
        { id: 'S2', member: 'CD', t: 1, kind: 'fixed', angle: 90 },
    ]);
    assert.deepEqual(original.loads, [
        { id: 'q1', member: 'BC', kind: 'distributed', t: 0, end: 1, fx: 0, fy: -5, mz: 0, qEnd: -5 },
    ]);
    assert.equal(artifact.members[2].geometry.dy.numerator, '-4');
    assert.deepEqual(artifact.members.map(member => member.endLaws.map(law => law.effectiveReference)),
        [['AB', 'AB'], ['AB', 'BC'], ['BC', 'CD']]);
    assert.equal(trace.binding.rawSource, trace.identity.rawExportSha256);
    assert.equal(artifact.bindings.mechanical, envelope.bindings.mechanical);
    assert.equal(artifact.status, 'pending-not-formally-verified');
    assert.equal(artifact.bindings.checker, null);
    assert.equal(artifact.bindings.result, null);
    assert.match(leanSource, new RegExp(artifact.artifactDigest));
});

test('bound trace is deterministic and retains the loaded numerical recovery', async () => {
    const first = await buildPortalPilot(), second = await buildPortalPilot();
    assert.deepEqual(first, second);
    const result = first.trace.numerical;
    assert.equal(result.engineStatus, 'stable');
    assert.ok(Math.abs(result.reactions[0].fy - 15) < 1e-7);
    assert.ok(Math.abs(result.reactions[1].fy - 15) < 1e-7);
    assert.ok(result.beamMidpoint.uy < 0);
    assert.ok(result.beamMidpoint.M > 0);
    // Removing the distributed source must not leave the same bending field.
    assert.equal(first.artifact.members[1].intervals[0].contributions[0].sourceId, 'q1');
    assert.equal(first.trace.formalInstance.globalSolutionCertificate, 'not-constructed');
});

test('recomputation rejects reversed-axis, omitted-load and moved-support artifacts', async () => {
    const { envelope, artifact } = await buildPortalPilot();
    for (const mutate of [
        copy => { copy.members[2].geometry.sine.args[0].numerator = '4'; },
        copy => { copy.members[1].intervals[0].verticalEndpoints[0].numerator = '0'; },
        copy => { copy.supports[1].location.end = 'a'; },
    ]) {
        const altered = structuredClone(artifact);
        mutate(altered);
        await assert.rejects(verifyExactCutArtifact(envelope, altered), /does not match/);
    }
});

test('finite witness template refuses an omitted distributed source or support', async () => {
    const { trace, artifact } = await buildPortalPilot();
    const missingLoad = structuredClone(artifact);
    missingLoad.members[1].intervals[0].contributions = [];
    assert.throws(() => validatePortalTopology(trace.identity.unchangedOriginalModel, missingLoad));
    const missingSupport = structuredClone(artifact);
    missingSupport.supports.pop();
    assert.throws(() => validatePortalTopology(trace.identity.unchangedOriginalModel, missingSupport));
});
