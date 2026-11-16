/** Synthetic native-checker fixtures. Generation is not checker acceptance. */
import { registerHooks } from 'node:module';
import { mkdirSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { resolve } from 'node:path';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { proposeInclinedPacket } = await import('../../web/frame-interval-packet.ts');
const { frameQueryConvention } = await import('../../web/frame-candidate.ts');
const directory = resolve(process.argv[2] ?? '.data/inclined-frame-packets');
mkdirSync(directory, { recursive: true });
const manifest = [];
function save(name, packet, expected, request) {
    const bytes = typeof packet === 'string' ? Buffer.from(packet) : packet;
    writeFileSync(resolve(directory, name + '.txt'), bytes);
    const entry = { name, expected, bytes: bytes.length,
        sha256: createHash('sha256').update(bytes).digest('hex') };
    if (request) {
        const requestBytes = JSON.stringify(request);
        writeFileSync(resolve(directory, name + '.request.json'), requestBytes);
        entry.requestSha256 = createHash('sha256').update(requestBytes).digest('hex');
    }
    manifest.push(entry);
}

// 1. Irrational original member length, arbitrary global point force.
const source = {
    nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 1, y: 2 }],
    members: [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }],
    supports: [{ id: 'S', member: 'AB', kind: 'fixed', t: 0, angle: 90 }],
    loads: [{ id: 'P', member: 'AB', kind: 'force', t: 1, end: 1, fx: 3, fy: -7, mz: 0, qEnd: 0 }],
};
const query = { member: 'AB', parameter: 1, cutSide: 'left', ...frameQueryConvention };
const proposed = proposeInclinedPacket(source, query, 96);
save('irrational-cantilever', proposed.packet, 'accept', { model: source, query });

// 2. Sign-changing affine loading with zero resultant and nonzero moment.
const affine = structuredClone(source);
affine.loads = [{ id: 'w', member: 'AB', kind: 'distributed', t: 0, end: 1,
    fx: 0, fy: -5, mz: 0, qEnd: 5 }];
const interiorQuery = { ...query, parameter: 0.5 };
save('affine-zero-resultant', proposeInclinedPacket(affine, interiorQuery, 96).packet, 'accept',
    { model: affine, query: interiorQuery });

const reversed = structuredClone(source);
reversed.members[0].a = 'B'; reversed.members[0].b = 'A';
reversed.supports[0].t = 1;
reversed.loads[0].t = reversed.loads[0].end = 0;
const reversedEndQuery = { ...query, parameter: 0, cutSide: 'right' };
save('reversed-cantilever', proposeInclinedPacket(reversed, reversedEndQuery, 96).packet, 'accept',
    { model: reversed, query: reversedEndQuery });
save('cantilever-interior', proposeInclinedPacket(source,
    interiorQuery, 96).packet, 'accept', { model: source, query: interiorQuery });
save('reversed-interior', proposeInclinedPacket(reversed,
    interiorQuery, 96).packet, 'accept', { model: reversed, query: interiorQuery });

// A shared rigid point splits the same physical cantilever into two members.
const shared = structuredClone(source);
shared.nodes.push({ id: 'C', x: 2, y: 4 });
shared.members.push({ id: 'BC', a: 'B', b: 'C', EA: 2000000, EI: 20000 });
shared.loads[0].member = 'BC';
const sharedQuery = { ...query, member: 'BC' };
save('shared-rigid-joint', proposeInclinedPacket(shared, sharedQuery, 96).packet, 'accept',
    { model: shared, query: sharedQuery });

const roller = structuredClone(source);
roller.supports = [
    { id: 'A-pin', member: 'AB', kind: 'pin', t: 0, angle: 90 },
    { id: 'B-roller', member: 'AB', kind: 'roller', t: 1, angle: 37 },
    { id: 'B-alias', member: 'AB', kind: 'roller', t: 1, angle: 217 },
];
roller.loads[0].t = roller.loads[0].end = 0.5;
for (const cutSide of ['left', 'right']) {
    const rollerQuery = { ...query, parameter: 0.5, cutSide };
    save('roller-interior-' + cutSide, proposeInclinedPacket(roller, rollerQuery, 96).packet, 'accept',
        { model: roller, query: rollerQuery });
}

// 3. Root, inverse, protocol and preallocation failures must grant no result.
const original = new TextDecoder().decode(proposed.packet);
const tokens = original.split('\n');
const rootStart = tokens.length - 2 * (proposed.coordinates ** 2 + proposed.coordinates) - 4;
const badRoot = [...tokens];
badRoot.splice(rootStart, 4, '0', '1', '0', '1');
save('invalid-root', badRoot.join('\n'), 'reject');
const zeroInverse = [...tokens];
for (let index = 0; index < proposed.coordinates ** 2; index++) {
    zeroInverse[rootStart + 4 + 2 * index] = '0';
    zeroInverse[rootStart + 5 + 2 * index] = '1';
}
save('noncontracting-inverse', zeroInverse.join('\n'), 'reject');
save('wrong-header', original.replace('CV2011_INCLINED_1', 'CV2011_INCLINED_2'), 'reject');
save('trailing-field', original + '\n0', 'reject');
const invalidPrecision = [...tokens];
invalidPrecision[rootStart - 1] = '80';
save('invalid-precision', invalidPrecision.join('\n'), 'reject');
const zeroDenominator = [...tokens];
zeroDenominator[7] = '0';
save('zero-denominator', zeroDenominator.join('\n'), 'reject');
save('too-many-lines', Array.from({ length: 6001 }, () => '0').join('\n'), 'reject');
save('too-many-bytes', 'x'.repeat(1048577), 'reject');
writeFileSync(resolve(directory, 'manifest.json'), JSON.stringify(manifest, null, 2) + '\n');
console.log(JSON.stringify({ fixtures: manifest.length, directory, checker_executed: false }));
