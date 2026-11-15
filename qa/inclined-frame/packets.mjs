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
const directory = resolve('.data/inclined-frame-packets');
mkdirSync(directory, { recursive: true });
const manifest = [];
function save(name, packet, expected) {
    const bytes = typeof packet === 'string' ? Buffer.from(packet) : packet;
    writeFileSync(resolve(directory, name + '.txt'), bytes);
    manifest.push({ name, expected, bytes: bytes.length,
        sha256: createHash('sha256').update(bytes).digest('hex') });
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
save('irrational-cantilever', proposed.packet, 'accept');

// 2. Sign-changing affine loading with zero resultant and nonzero moment.
const affine = structuredClone(source);
affine.loads = [{ id: 'w', member: 'AB', kind: 'distributed', t: 0, end: 1,
    fx: 0, fy: -5, mz: 0, qEnd: 5 }];
save('affine-zero-resultant', proposeInclinedPacket(affine, { ...query, parameter: 0.5 }, 96).packet, 'accept');

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
