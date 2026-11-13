/** Produce deterministic accepted/rejected packets for the native Lean and
 * actual WASM suites. A filename's leading number is the expected ABI code:
 * 1 accepted, 0 failed exact checks, 2 malformed. These are test fixtures only.
 */
import { registerHooks } from 'node:module';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { example } = await import('../../web/engine.ts');
const { compileFrame, FrameCandidates, frameQueryConvention } = await import('../../web/frame-candidate.ts');
const { framePacket } = await import('../../web/frame-packet.ts');
const { one, zero, add, neg } = await import('../../web/frame-rational.ts');
const output = process.argv[2] ?? '.data/general-frame-packets';
await mkdir(output, { recursive: true });
const selected = (member, parameter = 0.5, cutSide = 'left') => ({ member, parameter, cutSide, ...frameQueryConvention });
const make = (source, query) => new FrameCandidates().produce(compileFrame(source, query));
const save = (name, source, query, certificate = make(source, query)) =>
    writeFile(join(output, name + '.packet'), framePacket(source, query, certificate));
const copy = value => structuredClone(value);

const beam = {
    nodes: [{ id: 'left', x: 0, y: 0 }, { id: 'right', x: 8, y: 0 }],
    members: [{ id: 'beam', a: 'left', b: 'right', EA: 2000000, EI: 20000 }],
    supports: [{ id: 'a', member: 'beam', t: 0, kind: 'pin', angle: 90 },
        { id: 'b', member: 'beam', t: 0.5, kind: 'roller', angle: 90 },
        { id: 'c', member: 'beam', t: 1, kind: 'roller', angle: 90 }],
    loads: [{ id: 'w', member: 'beam', kind: 'distributed', t: 0, end: 1, fx: 0, fy: -5, mz: 0, qEnd: -5 }],
};
const query = selected('beam'), baseline = make(beam, query);
await save('1_two_spans', beam, query, baseline);
const joinedBeam = {
    nodes: [beam.nodes[0], { id: 'middle', x: 4, y: 0 }, beam.nodes[1]],
    members: [{ ...beam.members[0], id: 'first', b: 'middle' },
        { ...beam.members[0], id: 'second', a: 'middle' }],
    supports: [{ ...beam.supports[0], member: 'first' },
        { ...beam.supports[1], member: 'first', t: 1 }, { ...beam.supports[2], member: 'second' }],
    loads: [{ ...beam.loads[0], id: 'w1', member: 'first' }, { ...beam.loads[0], id: 'w2', member: 'second' }],
};
await save('1_two_original_members', joinedBeam, selected('first', 1));
const reversed = copy(beam);
[reversed.members[0].a, reversed.members[0].b] = [reversed.members[0].b, reversed.members[0].a];
reversed.supports.forEach(support => { support.t = 1 - support.t; });
await save('1_reversed_member', reversed, selected('beam', 0.5, 'right'));
const duplicate = copy(beam);
duplicate.supports.push({ ...duplicate.supports[1], id: 'duplicate-interior-restraint' });
await save('1_duplicate_restraint', duplicate, query);
const fullyRestrained = copy(beam);
fullyRestrained.supports = [0, 1].map((t, index) => ({ id: 'fixed-' + index, member: 'beam', t, kind: 'fixed', angle: 90 }));
await save('1_loaded_zero_free_space', fullyRestrained, query);
const disconnected = copy(joinedBeam);
disconnected.nodes = [
    { id: 'a1', x: 0, y: 0 }, { id: 'b1', x: 4, y: 0 },
    { id: 'a2', x: 0, y: 0 }, { id: 'b2', x: 4, y: 0 },
];
disconnected.members[0].a = 'a1'; disconnected.members[0].b = 'b1';
disconnected.members[1].a = 'a2'; disconnected.members[1].b = 'b2';
disconnected.supports = ['first', 'second'].flatMap(member => [
    { id: member + '-a', member, t: 0, kind: 'pin', angle: 90 },
    { id: member + '-b', member, t: 1, kind: 'roller', angle: 90 },
]);
disconnected.loads = [disconnected.loads[0]];
await save('1_coincident_disconnected_members', disconnected, selected('first'));
await save('1_original_portal', example('frame'), selected('BC'));
// Public synthetic affine drawings; screenshot geometry was not supplied.
const affinePortal = example('frame');
affinePortal.loads[0].fy = -5; affinePortal.loads[0].qEnd = 5;
await save('1_affine_portal', affinePortal, selected('BC', 0.25));
await save('1_affine_zero_crossing_left', affinePortal, selected('BC', 0.5, 'left'));
await save('1_affine_zero_crossing_right', affinePortal, selected('BC', 0.5, 'right'));
const affineBeam = copy(beam);
affineBeam.nodes[1].x = 6;
affineBeam.supports.splice(1, 1);
affineBeam.loads[0].qEnd = 5;
await save('1_affine_zero_resultant', affineBeam, selected('beam'));
const affineReversed = copy(affineBeam);
[affineReversed.members[0].a, affineReversed.members[0].b] = [affineReversed.members[0].b, affineReversed.members[0].a];
affineReversed.supports.forEach(support => { support.t = 1 - support.t; });
[affineReversed.loads[0].fy, affineReversed.loads[0].qEnd] = [affineReversed.loads[0].qEnd, affineReversed.loads[0].fy];
await save('1_affine_reversed', affineReversed, selected('beam', 0.75, 'right'));
const affineOverlap = copy(affineBeam);
affineOverlap.loads[0].t = 0.25; affineOverlap.loads[0].end = 0.75;
affineOverlap.loads.push({ ...affineOverlap.loads[0], id: 'overlap-affine', t: 0.5, end: 1, fy: 2, qEnd: -2 });
affineOverlap.supports.push({ ...beam.supports[1], id: 'middle-affine' });
await save('1_affine_overlap_left', affineOverlap, selected('beam', 0.5, 'left'));
await save('1_affine_overlap_right', affineOverlap, selected('beam', 0.5, 'right'));
for (const vertical of [false, true]) {
    const fixedAffine = copy(affineBeam);
    fixedAffine.supports.forEach(support => { support.kind = 'fixed'; });
    if (vertical) { fixedAffine.nodes[1].x = 0; fixedAffine.nodes[1].y = 6; }
    await save('1_affine_fixed_' + (vertical ? 'axial' : 'bending'), fixedAffine, selected('beam', 0.25));
}
const staleAffine = make(affineBeam, selected('beam'));
affineBeam.loads[0].qEnd = 6;
await save('0_affine_changed_endpoint', affineBeam, selected('beam'), staleAffine);
affineBeam.loads[0].qEnd = 5; affineBeam.loads[0].t = 0.25;
await save('0_affine_changed_interval', affineBeam, selected('beam'), staleAffine);
const permuted = example('frame');
for (const field of ['nodes', 'members', 'supports', 'loads']) permuted[field].reverse();
await save('1_permuted_portal_records', permuted, selected('BC'));
const resized = example('frame');
resized.nodes[1].y = resized.nodes[2].y = 3.25;
resized.nodes[2].x = resized.nodes[3].x = 7.5;
resized.members[0].EA = 3000000;
resized.members[1].EI = 30000;
resized.supports[0].kind = 'pin';
resized.loads.push({ id: 'horizontal', member: 'BC', kind: 'force', t: 0, end: 1, fx: 7, fy: 0, mz: 0, qEnd: 0 });
await save('1_resized_portal', resized, selected('BC', 0.1));
const edited = copy(beam);
edited.nodes[1].x = 10;
edited.supports[1].t = 0.375;
edited.loads[0].t = 0.25; edited.loads[0].end = 0.75;
edited.loads.push({ ...edited.loads[0], id: 'overlap', t: 0.375, end: 1, fy: -2, qEnd: -2 });
edited.loads.push({ id: 'couple', member: 'beam', kind: 'moment', t: 0.625, end: 1, fx: 0, fy: 0, mz: 3, qEnd: 0 });
await save('1_overlap_couple_left', edited, selected('beam', 0.625, 'left'));
await save('1_overlap_couple_right', edited, selected('beam', 0.625, 'right'));
const decimal = copy(edited);
decimal.supports[1].t = 0.4;
decimal.loads[0].t = 0.2; decimal.loads[0].end = 0.8;
decimal.loads[1].t = 0.4;
decimal.loads[2].t = 0.6;
await save('1_common_decimal_edits', decimal, selected('beam', 0.6));
const singular = copy(beam);
singular.supports = []; singular.loads = [];
await save('1_zero_load_mechanism', singular, query);
const zeroMechanism = make(singular, query);
zeroMechanism.motion.fill(zero);
await save('0_zero_null_vector', singular, query, zeroMechanism);
singular.loads = copy(beam.loads);
await save('1_loaded_mechanism', singular, query);

for (const [name, mutate] of [
    ['motion', c => { c.motion[2] = add(c.motion[2], one); }],
    ['reaction', c => { c.reactions[1] = add(c.reactions[1], one); }],
    ['field', c => { c.readouts[5] = zero; c.readouts[2] = add(c.readouts[2], one); }],
    ['factor', c => { c.lower[1][0] = add(c.lower[1][0], one); }],
    ['pivot', c => { c.diagonal[0] = neg(c.diagonal[0]); }],
    ['point_order', c => { [c.points[0], c.points[1]] = [c.points[1], c.points[0]]; }],
    ['point_parameter', c => { c.points[2].t = zero; }],
    ['point_coordinate', c => { c.points[2].x = add(c.points[2].x, one); }],
]) {
    const corrupted = copy(baseline); mutate(corrupted);
    await save('0_corrupt_' + name, beam, query, corrupted);
}
const omitted = copy(beam); omitted.loads = [];
await save('0_omitted_load', beam, query, make(omitted, query));
await save('0_stale_query', beam, selected('beam', 0.25), baseline);
await save('0_wrong_query_side', beam, selected('beam', 0.5, 'right'), baseline);
const wrongRestraint = copy(beam); wrongRestraint.supports[1].angle = 0;
await save('0_changed_restraint_direction', wrongRestraint, query, baseline);
const changedOwnership = copy(joinedBeam); changedOwnership.loads[1].member = 'first';
await save('0_changed_load_owner', changedOwnership, selected('first', 1), make(joinedBeam, selected('first', 1)));
const packet = new TextDecoder().decode(framePacket(beam, query, baseline));
for (const [name, text] of [
    ['header', packet.replace('CV2011_FRAME_1', 'CV2011_FRAME_2')],
    ['count', packet.replace('CV2011_FRAME_1\n2', 'CV2011_FRAME_1\n999')],
    ['extra', packet + '\n0'],
    ['zero_denominator', packet.replace('\n0\n1\n', '\n0\n0\n')],
    ['noncanonical', packet.replace('\n0\n1\n', '\n-0\n1\n')],
    ['source_digits', packet.replace('\n0\n1\n', '\n1' + '0'.repeat(128) + '\n1\n')],
    ['witness_digits', packet.slice(0, -3) + '1' + '0'.repeat(128) + '\n1'],
]) await writeFile(join(output, '2_' + name + '.packet'), text);
console.log('Wrote source/witness packets to ' + output);
