/** Reproduce the shipped portal example without editing or replacing its model.
 * Run: node scripts/portal-frame-pilot.mjs qa/local-portal-pilot
 * Outputs are public example data, an untrusted trace and a Lean instance to
 * check in Linux CI. This script never executes Lean or changes UI status. */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile, mkdir, writeFile } from 'node:fs/promises';
import { registerHooks } from 'node:module';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { emitExactExpression } from './exact-geometry-expressions.mjs';

registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { example, analyse } = await import('../web/engine.ts');
const { createEvidenceEnvelope, parseEvidenceModel } = await import('../web/model-evidence.ts');
const { adaptEvidenceSnapshot, verifyExactCutArtifact, exactBinary64 } = await import('../web/exact-cut-adapter.ts');

const BASELINE = '584d32e1d78fc6e2c7baf439e5c048170a687f21';
const BASELINE_ENGINE_SHA256 = '90c90f26aa1e806cbca6b1bb324212837c5ba194537a3ec81ae9d01351cc6799';
const sha256 = text => createHash('sha256').update(text).digest('hex');
const json = value => JSON.stringify(value, null, 2) + '\n';
const vector = values => `![${values.join(', ')}]`;
const realVector = values => vector(values.map(emitExactExpression));

/** Emit only bounded indices. No source ID or arbitrary text enters Lean. */
function finiteIndex(index, count) {
    assert.ok(Number.isSafeInteger(index) && index >= 0 && index < count);
    return String(index);
}

function endLocation(location) {
    assert.equal(location.kind, 'endSide', 'This pilot has no interior cuts');
    assert.ok(location.end === 'a' || location.end === 'b');
    return `.endSide (${finiteIndex(location.memberIndex, 3)}, ${location.end === 'b'})`;
}

/** These guards bound the witness template to the original portal topology.
 * Values, incidence, axes and loads are still emitted from the actual adapter. */
export function validatePortalTopology(model, artifact) {
    assert.deepEqual(model.nodes.map(node => node.id), ['A', 'B', 'C', 'D']);
    assert.deepEqual(model.members.map(member => [member.id, member.a, member.b]),
        [['AB', 'A', 'B'], ['BC', 'B', 'C'], ['CD', 'C', 'D']]);
    assert.equal(artifact.nodes.length, 4);
    assert.equal(artifact.members.length, 3);
    assert.equal(artifact.actions.length, 0);
    assert.equal(artifact.supports.length, 2);
    assert.equal(model.loads.length, 1);
    assert.deepEqual(model.loads.map(load => [load.id, load.member, load.kind, load.t, load.end]),
        [['q1', 'BC', 'distributed', 0, 1]]);
    assert.deepEqual(model.supports.map(support => [support.id, support.member, support.t, support.kind]),
        [['S1', 'AB', 0, 'fixed'], ['S2', 'CD', 1, 'fixed']]);
    for (const node of artifact.nodes) {
        assert.equal(node.joint, 'rigid');
        assert.equal(node.rotationStiffness, null);
        assert.equal(node.requestedReference, null);
    }
    for (const [index, member] of artifact.members.entries()) {
        assert.equal(member.index, index);
        assert.deepEqual(member.cuts.map(cut => cut.parameter),
            [{ numerator: '0', denominator: '1' }, { numerator: '1', denominator: '1' }]);
        assert.equal(member.intervals.length, 1);
        const interval = member.intervals[0];
        assert.equal(interval.memberIndex, index);
        assert.equal(interval.contributions.length, index === 1 ? 1 : 0);
        assert.equal(member.cuts[0].location.memberIndex, index);
        assert.equal(member.cuts[1].location.memberIndex, index);
        assert.equal(member.cuts[0].location.end, 'a');
        assert.equal(member.cuts[1].location.end, 'b');
        assert.deepEqual(interval.left, member.cuts[0].location);
        assert.deepEqual(interval.right, member.cuts[1].location);
        for (const law of member.endLaws) {
            for (const direction of ['axial', 'transverse', 'rotation']) assert.equal(law[direction].kind, 'rigid');
        }
        assert.equal(model.members[index].connectionA, undefined);
        assert.equal(model.members[index].connectionB, undefined);
    }
    const contribution = artifact.members[1].intervals[0].contributions[0];
    assert.equal(contribution.sourceIndex, 0);
    assert.equal(contribution.sourceId, model.loads[0].id);
    assert.deepEqual(artifact.supports.map(support => [support.location.memberIndex, support.location.end, support.kind]),
        [[0, 'a', 'fixed'], [2, 'b', 'fixed']]);
}

/** Bind every finite-model field to the adapter and fill a fixed proof template. */
async function emitPortalInstance(model, artifact) {
    validatePortalTopology(model, artifact);
    const members = artifact.members;
    const intervals = members.map(member => member.intervals[0]);
    const nodeIndex = id => finiteIndex(artifact.nodes.findIndex(node => node.id === id), 4);
    const point = value => `(${emitExactExpression(value.x)}, ${emitExactExpression(value.y)})`;
    const contribution = intervals[1].contributions[0];
    const fields = {
        ARTIFACT_DIGEST: artifact.artifactDigest,
        NODES: vector(model.nodes.map(node => point({ x: exactBinary64(node.x), y: exactBinary64(node.y) }))),
        START_NODES: vector(members.map(member => nodeIndex(member.startNodeId))),
        END_NODES: vector(members.map(member => nodeIndex(member.endNodeId))),
        COSINES: realVector(members.map(member => member.geometry.cosine)),
        SINES: realVector(members.map(member => member.geometry.sine)),
        LEFT_LOCATIONS: vector(intervals.map(interval => endLocation(interval.left))),
        RIGHT_LOCATIONS: vector(intervals.map(interval => endLocation(interval.right))),
        LENGTHS: realVector(intervals.map(interval => interval.length)),
        EA: realVector(intervals.map(interval => interval.EA)),
        EI: realVector(intervals.map(interval => interval.EI)),
        MEMBER_EA: realVector(model.members.map(member => exactBinary64(member.EA))),
        MEMBER_EI: realVector(model.members.map(member => exactBinary64(member.EI))),
        Q_START: realVector(intervals.map(interval => interval.verticalEndpoints[0])),
        Q_END: realVector(intervals.map(interval => interval.verticalEndpoints[1])),
        SEGMENT_STARTS: vector(members.map(member => point(member.cuts[0].position))),
        SEGMENT_ENDS: vector(members.map(member => point(member.cuts[1].position))),
        SUPPORTS: vector(artifact.supports.map(support =>
            `⟨${endLocation(support.location)}, .fixed, ${emitExactExpression(support.axes.cosine)}, ${emitExactExpression(support.axes.sine)}, false, false, false⟩`)),
        ANGLES: realVector(artifact.supports.map(support => support.axes.angleDegrees)),
        SOURCE_A: emitExactExpression(exactBinary64(model.loads[contribution.sourceIndex].t)),
        SOURCE_B: emitExactExpression(exactBinary64(model.loads[contribution.sourceIndex].end)),
        SOURCE_Q_START: emitExactExpression(exactBinary64(model.loads[contribution.sourceIndex].fy)),
        SOURCE_Q_END: emitExactExpression(exactBinary64(model.loads[contribution.sourceIndex].qEnd)),
        RESULTANT: emitExactExpression(intervals[1].resultant),
        GLOBAL_MOMENT: emitExactExpression(intervals[1].globalMomentAboutOrigin),
    };
    assert.match(fields.ARTIFACT_DIGEST, /^[a-f0-9]{64}$/);
    const template = await readFile(new URL('./portal-frame-instance.lean.txt', import.meta.url), 'utf8');
    const source = template.replace(/@@([A-Z_]+)@@/g, (_, name) => {
        assert.ok(Object.hasOwn(fields, name), `Missing template field ${name}`);
        return fields[name];
    });
    assert.ok(!source.includes('@@'));
    return source;
}

/** Numerical diagnostics refer only to the existing floating-point engine. */
function numericalTrace(model) {
    const analysis = analyse(model);
    assert.equal(analysis.status, 'stable');
    assert.equal(analysis.elements.length, 3);
    const endpoints = analysis.elements.map(element => ({
        member: element.member, start: element.samples[0], end: element.samples.at(-1),
    }));
    const beam = analysis.elements.find(element => element.member === 'BC');
    const midpoint = beam.samples.find(sample => sample.t === 0.5);
    assert.ok(midpoint, 'The existing 41-sample recovery includes the midpoint');
    const totalReaction = analysis.reactions.reduce((total, reaction) => ({
        fx: total.fx + reaction.fx,
        fy: total.fy + reaction.fy,
        moment: total.moment + reaction.mz + reaction.x * reaction.fy - reaction.y * reaction.fx,
    }), { fx: 0, fy: 0, moment: 0 });
    const load = model.loads[0];
    const beamStart = model.nodes.find(node => node.id === 'B');
    const beamEnd = model.nodes.find(node => node.id === 'C');
    const length = Math.hypot(beamEnd.x - beamStart.x, beamEnd.y - beamStart.y);
    const verticalLoad = length * (load.fy + load.qEnd) / 2;
    const loadMoment = verticalLoad * (beamStart.x + beamEnd.x) / 2;
    const balance = { fx: totalReaction.fx, fy: totalReaction.fy + verticalLoad,
        momentAboutA: totalReaction.moment + loadMoment };
    const continuity = [0, 1].map(index => ({
        node: index === 0 ? 'B' : 'C',
        ux: endpoints[index].end.ux - endpoints[index + 1].start.ux,
        uy: endpoints[index].end.uy - endpoints[index + 1].start.uy,
        rotation: endpoints[index].end.rotation - endpoints[index + 1].start.rotation,
    }));
    for (const value of Object.values(balance)) assert.ok(Math.abs(value) < 1e-7);
    for (const row of continuity) {
        for (const key of ['ux', 'uy', 'rotation']) assert.ok(Math.abs(row[key]) < 1e-10);
    }
    for (const sample of [endpoints[0].start, endpoints[2].end]) {
        for (const key of ['ux', 'uy', 'rotation']) assert.ok(Math.abs(sample[key]) < 1e-10);
    }
    return { status: 'numerical-only-not-a-formal-solution-certificate', engineStatus: analysis.status,
        units: 'm, kN, kN m, radians; global y upward, rotation counterclockwise',
        engineResidual: analysis.residual, degree: analysis.degree, reactions: analysis.reactions,
        memberEndpoints: endpoints, beamMidpoint: midpoint, globalBalanceResiduals: balance,
        jointContinuityResiduals: continuity, checks: 'balance < 1e-7; continuity and fixed-base motions < 1e-10' };
}

/** Reproducible public fixture; parser defaults are recorded, never silently edited. */
export async function buildPortalPilot() {
    const engineSource = (await readFile(new URL('../web/engine.ts', import.meta.url), 'utf8')).replace(/\r\n/g, '\n');
    assert.equal(sha256(engineSource), BASELINE_ENGINE_SHA256, 'Pilot requires the accepted baseline engine source');
    const model = example('frame');
    const original = structuredClone(model);
    const rawSource = json({ version: 2, model });
    const query = { member: 'BC', parameter: 0.5, cutSide: 'left', quantity: 'M',
        units: 'kN m', signConvention: 'sagging positive' };
    const envelope = await createEvidenceEnvelope(model, query, rawSource);
    assert.deepEqual(envelope.model, parseEvidenceModel(original));
    const artifact = await adaptEvidenceSnapshot(envelope);
    await verifyExactCutArtifact(envelope, artifact);
    const leanSource = await emitPortalInstance(model, artifact);
    const numerical = numericalTrace(model);
    assert.deepEqual(model, original, 'Pilot must not mutate the shipped example');
    const trace = {
        schema: 'cv2011-portal-frame-pilot', version: 1,
        identity: { baseline: BASELINE, source: "web/engine.ts: example('frame')", menuLabel: 'Portal frame',
            sourceFileSha256LF: sha256(engineSource), rawExportSha256: sha256(rawSource),
            parserDefaults: 'Absent joint becomes rigid; absent custom-support flags become false. Mechanics are unchanged.',
            unchangedOriginalModel: original },
        binding: { ...envelope.bindings, artifactDigest: artifact.artifactDigest, generatedLeanSha256: sha256(leanSource),
            meaning: 'Digests identify inputs and emitted proof text; they are not a verified parser/emitter theorem.' },
        finiteEncoding: { nodes: 4, members: 3, interiorSlotsPerMember: 0, segments: 3, pointActions: 0, supports: 2,
            nodeOrder: artifact.nodes.map(node => node.id), memberOrder: artifact.members.map(member => member.id),
            segmentOwnership: 'segment i belongs to member i; one full [0,1] interval per member',
            queryIsNotAnExtraCut: true },
        exactInputs: { nodes: artifact.nodes, supports: artifact.supports, actions: artifact.actions,
            members: artifact.members.map(({ index, id, startNodeId, endNodeId, geometry, endLaws, cuts, intervals }) =>
                ({ index, id, startNodeId, endNodeId, geometry, endLaws, cuts, intervals })) },
        formalInstance: { status: 'emitted-not-checked-by-this-script',
            intendedChecks: ['finite structural witness', 'endpoint geometry correspondence', 'exact input contract',
                'fixed support rows and rigid end laws', 'distributed-load restriction and resultant',
                'consistent load virtual work', 'local recovery for arbitrary encoded end movements',
                'conditional equilibrium/reaction interface', 'standard axiom audit'],
            globalSolutionCertificate: 'not-constructed', browserStatus: artifact.status },
        numerical,
        unresolved: ['General parser, binary64 decoder, hashing and emitter correctness.',
            'General cut builder and finite encoding/source-provenance correctness; this is one explicit instance.',
            'A portal displacement vector bound to the exact Coordinate model, admissibility and equilibrium proof.',
            'Exact support-reaction and requested-section certificates for that vector; numerical engine equivalence and error bounds.'],
    };
    return { rawSource, envelope, artifact, leanSource, trace };
}

if (process.argv[1] && pathToFileURL(resolve(process.argv[1])).href === import.meta.url) {
    const target = process.argv[2];
    assert.ok(target, 'Provide an output directory');
    const pilot = await buildPortalPilot();
    await mkdir(target, { recursive: true });
    for (const [name, content] of Object.entries({ 'portal-model.json': pilot.rawSource,
        'envelope.json': json(pilot.envelope), 'adapter.json': json(pilot.artifact),
        'PortalFramePilot.lean': pilot.leanSource, 'trace.json': json(pilot.trace) })) {
        await writeFile(resolve(target, name), content, 'utf8');
    }
    console.log(`Portal example artifact ${pilot.artifact.artifactDigest}; Lean instance emitted, not locally checked.`);
}
