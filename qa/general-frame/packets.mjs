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
await save('1_original_portal', example('frame'), selected('BC'));
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
