import test from 'node:test';
import assert from 'node:assert/strict';
import { createEvidenceEnvelope } from '../web/model-evidence.ts';
import { registerHooks } from 'node:module';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { adaptEvidenceSnapshot, exactBinary64, verifyExactCutArtifact } = await import('../web/exact-cut-adapter.ts');

const query = { member: 'm', parameter: 0.5, cutSide: 'left', quantity: 'M', units: 'kN m', signConvention: 'sagging positive' };
const ratio = (numerator, denominator = '1') => ({ numerator: String(numerator), denominator: String(denominator) });
const model = () => ({
    nodes: [{ id: 'A', x: 2, y: 3 }, { id: 'B', x: 1, y: 5 }],
    members: [{ id: 'm', a: 'A', b: 'B', EA: 10, EI: 20 }],
    supports: [], loads: [],
});
const load = (id, t, end, fy, qEnd) => ({ id, member: 'm', kind: 'distributed', t, end, fx: 91, fy, mz: 83, qEnd });
const adapt = async drawing => adaptEvidenceSnapshot(await createEvidenceEnvelope(drawing, query));

test('binary64 bits decode exactly including zeros, subnormal and extreme values', () => {
    assert.deepEqual(exactBinary64(-0), ratio(0));
    assert.deepEqual(exactBinary64(Number.MIN_VALUE), ratio(1, (1n << 1074n).toString()));
    assert.deepEqual(exactBinary64(0.1), ratio('3602879701896397', '36028797018963968'));
    assert.deepEqual(exactBinary64(0.5 + 2 ** -53), ratio('4503599627370497', '9007199254740992'));
    assert.deepEqual(exactBinary64(Number.MAX_VALUE), ratio(((1n << 53n) - 1n) << 971n));
    assert.throws(() => exactBinary64(Infinity), /finite/);
});

test('exact cuts retain coincident sources and expose rounded merges and endpoint snaps', async () => {
    const drawing = model(), epsilon = 2 ** -30;
    drawing.supports = [
        { id: 'near-start', member: 'm', t: epsilon, kind: 'roller', angle: 90 },
        { id: 'middle', member: 'm', t: 0.5, kind: 'fixed', angle: 0 },
        { id: 'near-end', member: 'm', t: 1 - epsilon, kind: 'guided', angle: 37 },
    ];
    drawing.loads = [
        { id: 'F', member: 'm', kind: 'force', t: 0.5, end: 1, fx: 1, fy: -2, mz: 8, qEnd: 4 },
        { id: 'M', member: 'm', kind: 'moment', t: 0.5, end: 1, fx: 9, fy: 7, mz: 3, qEnd: 4 },
        load('q', 0.5, 0.5 + epsilon, -1, 1),
    ];
    const artifact = await adapt(drawing), member = artifact.members[0], diagnostic = artifact.discrepancies[0];
    assert.equal(member.cuts.length, 6);
    assert.deepEqual(member.cuts[2].sources.map(source => source.id), ['middle', 'F', 'M', 'q']);
    assert.deepEqual(member.cuts[2].sources.map(source => source.role), ['location', 'location', 'location', 'start']);
    assert.equal(member.cuts[1].location.kind, 'interior');
    assert.equal(member.cuts[4].location.kind, 'interior');
    assert.ok(diagnostic.mergedExactCuts.some(indices => indices.includes(2) && indices.includes(3)));
    assert.equal(diagnostic.cuts[1].endpointSnap, true);
    assert.equal(diagnostic.cuts[4].endpointSnap, true);
    assert.ok(diagnostic.loadBoundaryDifferences.some(item => item.sourceId === 'q' && item.role === 'end'));
    assert.equal(diagnostic.numericalGeometry, 'not-compared');
    assert.equal(artifact.status, 'pending-not-formally-verified');
});

test('overlapping signed affine loads use exact restrictions and retain cancellation provenance', async () => {
    const drawing = model();
    drawing.loads = [load('first', 0.25, 0.75, -2, 2), load('second', 0.5, 1, 2, -2), load('third', 0.25, 1, 0, 1)];
    const artifact = await adapt(drawing), intervals = artifact.members[0].intervals;
    const segment = intervals.find(item => item.from.numerator === '1' && item.from.denominator === '2');
    assert.deepEqual(segment.contributions.map(item => item.sourceId), ['first', 'second', 'third']);
    assert.deepEqual(segment.contributions[0].restrictedEndpoints, [ratio(0), ratio(2)]);
    assert.deepEqual(segment.contributions[1].restrictedEndpoints, [ratio(2), ratio(0)]);
    assert.deepEqual(segment.contributions[2].restrictedEndpoints, [ratio(1, 3), ratio(2, 3)]);
    assert.deepEqual(segment.verticalEndpoints, [ratio(7, 3), ratio(8, 3)]);
    assert.equal(segment.resultant.op, 'multiply');
    assert.equal(segment.firstMomentAboutOriginalStart.op, 'multiply');
    assert.equal(segment.globalMomentAboutOrigin.op, 'multiply');
    assert.deepEqual(artifact.members[0].geometry.dx, ratio(-1));
    assert.deepEqual(artifact.members[0].geometry.dy, ratio(2));
    assert.equal(artifact.members[0].geometry.length.op, 'sqrt');
    assert.equal(artifact.members[0].geometry.status, 'pending-exact-geometry');
});

test('member ownership, ordered reference fallback, releases and symbolic support axes survive', async () => {
    const drawing = model();
    drawing.nodes.push({ id: 'C', x: 0, y: 1 });
    drawing.nodes[0].joint = 'pinned';
    drawing.members.push({ id: 'cross', a: 'A', b: 'C', EA: 4, EI: 5, connectionA: { axial: 'free', transverse: 7, rotation: 'free' } });
    drawing.supports = [{ id: 'S', member: 'cross', t: 0, kind: 'guided', angle: 37 }];
    drawing.loads = [{ id: 'couple', member: 'cross', kind: 'moment', t: 0, end: 1, fx: 9, fy: 8, mz: 4, qEnd: 0 },
        { id: 'force', member: 'm', kind: 'force', t: 0.5, end: 1, fx: 2, fy: 1, mz: 7, qEnd: 0 },
        { id: 'force2', member: 'cross', kind: 'force', t: 0.5, end: 1, fx: 1, fy: 2, mz: 7, qEnd: 0 }];
    const result = await adapt(drawing), first = result.members[0], second = result.members[1];
    assert.notDeepEqual(first.cuts[1].location, second.cuts[1].location);
    assert.equal(second.endLaws[0].effectiveReference, 'm');
    assert.equal(second.endLaws[0].referenceReason, 'first-incident');
    assert.equal(second.endLaws[0].reason, 'explicit');
    assert.equal(second.endLaws[0].axial.kind, 'free');
    assert.equal(second.endLaws[0].transverse.kind, 'spring');
    assert.equal(result.actions[0].location.memberIndex, 1);
    assert.deepEqual(result.actions[0].components, { fx: ratio(0), fy: ratio(0), mz: ratio(4) });
    assert.deepEqual(result.actions.map(item => item.id), ['couple', 'force', 'force2']);
    assert.equal(result.supports[0].axes.cosine.op, 'cos');
    assert.equal(result.supports[0].axes.status, 'pending-exact-trigonometry');
    const explicit = structuredClone(drawing); explicit.nodes[0].referenceMember = 'cross';
    const changed = await adapt(explicit);
    assert.equal(changed.members[1].endLaws[0].reason, 'reference-rigid');
    assert.equal(changed.members[1].endLaws[0].referenceReason, 'requested');
});

test('bindings are deterministic, stale snapshots are rejected and inputs stay immutable', async () => {
    const drawing = model(), before = structuredClone(drawing), envelope = await createEvidenceEnvelope(drawing, query);
    const first = await adaptEvidenceSnapshot(envelope), second = await adaptEvidenceSnapshot(envelope);
    assert.equal(first.artifactDigest, second.artifactDigest);
    assert.match(first.artifactDigest, /^[a-f0-9]{64}$/);
    assert.equal(first.bindings.mechanical, envelope.bindings.mechanical);
    assert.equal(first.bindings.checker, null);
    assert.equal(first.bindings.result, null);
    assert.equal(first.members[0].obligations.length, 16);
    assert.ok(first.members[0].obligations.every(item => item.checkedInstance === false));
    assert.deepEqual(drawing, before);
    assert.ok(Object.isFrozen(first.members[0].cuts));
    const stale = structuredClone(envelope); stale.model.members[0].EI = 21;
    await assert.rejects(adaptEvidenceSnapshot(stale), /Stale mechanical/);
    const malformed = structuredClone(drawing); malformed.supports = [{ id: 'bad', member: 'm', t: 1.01, kind: 'pin', angle: 0 }];
    await assert.rejects(createEvidenceEnvelope(malformed, query), /between 0 and 1/);
});


test('changed load contribution, Jacobian, orientation or ownership is rejected', async () => {
    const drawing = model();
    drawing.loads = [load('q', 0.25, 1, -2, 4)];
    drawing.supports = [{ id: 'S', member: 'm', t: 0.5, kind: 'roller', angle: 37 }];
    const snapshot = await createEvidenceEnvelope(drawing, query);
    const artifact = await adaptEvidenceSnapshot(snapshot);
    await verifyExactCutArtifact(snapshot, artifact);
    for (const mutate of [
        candidate => { candidate.members[0].intervals[1].verticalEndpoints[0].numerator = '99'; },
        candidate => { candidate.members[0].intervals[1].contributions[0].sourceId = 'wrong'; },
        candidate => { candidate.members[0].intervals[1].length.args[1].numerator = '99'; },
        candidate => { candidate.members[0].intervals[1].localAxialEndpoints[0].op = 'negate'; },
        candidate => { candidate.supports[0].location.memberIndex = 99; },
    ]) {
        const altered = structuredClone(artifact); mutate(altered);
        await assert.rejects(verifyExactCutArtifact(snapshot, altered), /does not match/);
    }
});

test('signed cancellation retains sources and global-origin moment retains member direction', async () => {
    const drawing = model();
    drawing.loads = [load('positive', 0, 1, 1, 1), load('negative', 0, 1, -1, -1)];
    const cancelled = (await adapt(drawing)).members[0].intervals[0];
    assert.deepEqual(cancelled.verticalEndpoints, [ratio(0), ratio(0)]);
    assert.deepEqual(cancelled.contributions.map(item => item.sourceId), ['positive', 'negative']);
    drawing.loads.pop();
    const unit = (await adapt(drawing)).members[0].intervals[0];
    assert.deepEqual(unit.resultant.args[1], ratio(1));
    assert.deepEqual(unit.firstMomentAboutOriginalStart.args[1], ratio(1, 2));
    // x(t)=2-t, so the vertical load moment about the global origin is L*(2-1/2).
    assert.deepEqual(unit.globalMomentAboutOrigin.args[1], ratio(3, 2));
});

test('crossings stay member-owned and default joint laws remain explicit', async () => {
    const drawing = model();
    drawing.nodes = [{ id: 'A', x: 0, y: 0, joint: 'semi-rigid' }, { id: 'B', x: 2, y: 2 },
        { id: 'C', x: 0, y: 2 }, { id: 'D', x: 2, y: 0 }, { id: 'E', x: -1, y: 0 }];
    drawing.members = [{ id: 'm', a: 'A', b: 'B', EA: 1, EI: 1 },
        { id: 'other', a: 'C', b: 'D', EA: 1, EI: 1 }, { id: 'branch', a: 'A', b: 'E', EA: 1, EI: 1 }];
    drawing.loads = ['m', 'other'].map((member, index) => ({ id: `P${index}`, member, kind: 'force', t: 0.5,
        end: 1, fx: 1, fy: 0, mz: 0, qEnd: 0 }));
    const artifact = await adapt(drawing);
    assert.notDeepEqual(artifact.members[0].cuts[1].location, artifact.members[1].cuts[1].location);
    assert.equal(artifact.members[2].endLaws[0].reason, 'semi-rigid-default');
    assert.deepEqual(artifact.members[2].endLaws[0].rotation.stiffness, ratio(20000));
    assert.equal(artifact.members[0].endLaws[0].reason, 'reference-rigid');
});
