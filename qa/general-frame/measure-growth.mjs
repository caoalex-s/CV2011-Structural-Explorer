/** Isolated exact-arithmetic resource experiment; production limits stay fixed.
 * Copies the three candidate modules under .data, instruments digit growth,
 * and compares the same cases at 128, 256 and 512 digits. No Lean/WASM runs here.
 */
import { registerHooks } from 'node:module';
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { resolve, join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { performance } from 'node:perf_hooks';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { example } = await import('../../web/engine.ts');
const destination = resolve(process.argv[2] ?? '.data/general-frame-growth');
await mkdir(destination, { recursive: true });
const beam = {
    nodes: [{ id: 'left', x: 0, y: 0 }, { id: 'right', x: 8, y: 0 }],
    members: [{ id: 'beam', a: 'left', b: 'right', EA: 2000000, EI: 20000 }],
    supports: [{ id: 'a', member: 'beam', t: 0, kind: 'pin', angle: 90 },
        { id: 'b', member: 'beam', t: 0.5, kind: 'roller', angle: 90 },
        { id: 'c', member: 'beam', t: 1, kind: 'roller', angle: 90 }],
    loads: [{ id: 'w', member: 'beam', kind: 'distributed', t: 0, end: 1, fx: 0, fy: -5, mz: 0, qEnd: -5 }],
};
const decimalBeam = structuredClone(beam);
decimalBeam.nodes[1].x = 10;
decimalBeam.supports[1].t = 0.4;
decimalBeam.loads[0].t = 0.2; decimalBeam.loads[0].end = 0.8;
decimalBeam.loads.push({ ...decimalBeam.loads[0], id: 'overlap', t: 0.4, end: 1, fy: -2, qEnd: -2 });
decimalBeam.loads.push({ id: 'couple', member: 'beam', kind: 'moment', t: 0.6, end: 1, fx: 0, fy: 0, mz: 3, qEnd: 0 });
const portal = example('frame');
portal.nodes[1].y = portal.nodes[2].y = 3.25;
portal.nodes[2].x = portal.nodes[3].x = 7.5;
portal.members[0].EA = 3000000; portal.members[1].EI = 30000;
portal.supports[0].kind = 'pin';
portal.loads.push({ id: 'horizontal', member: 'BC', kind: 'force', t: 0, end: 1, fx: 7, fy: 0, mz: 0, qEnd: 0 });
const cases = [
    { name: 'two-span', model: beam, member: 'beam', parameter: 0.5 },
    { name: 'resized-portal', model: portal, member: 'BC', parameter: 0.1 },
    { name: 'decimal-interiors', model: decimalBeam, member: 'beam', parameter: 0.6 },
];
const sourceNames = ['frame-rational.ts', 'frame-candidate.ts', 'model-evidence.ts', 'frame-packet.ts'];
const source = Object.fromEntries(await Promise.all(sourceNames.map(async name => [name, await readFile(join('web', name), 'utf8')])));
const marker = '    const numerator = n / divisor, denominator = d / divisor;';
if (!source['frame-rational.ts'].includes(marker)) throw Error('Instrumentation location changed; review the experiment.');
const rows = [];
for (const cap of [128, 256, 512]) {
    const folder = join(destination, String(cap), 'web');
    await mkdir(folder, { recursive: true });
    for (const name of sourceNames) {
        let content = source[name];
        if (name === 'frame-rational.ts') content = content
            .replace('export const maxRationalDigits = 128;', `export const maxRationalDigits = ${cap};\nexport const digitGrowth = { normalized: 0, raw: 0 };`)
            .replace(marker, marker + '\n    const digits = (value: bigint) => (value < 0n ? -value : value).toString().length;\n    digitGrowth.normalized = Math.max(digitGrowth.normalized, digits(numerator), digits(denominator));\n    digitGrowth.raw = Math.max(digitGrowth.raw, digits(n), digits(d));');
        await writeFile(join(folder, name), content);
    }
    const arithmetic = await import(pathToFileURL(join(folder, 'frame-rational.ts')));
    const candidate = await import(pathToFileURL(join(folder, 'frame-candidate.ts')));
    const { framePacket } = await import(pathToFileURL(join(folder, 'frame-packet.ts')));
    for (const item of cases) {
        const query = { member: item.member, parameter: item.parameter, cutSide: 'left', ...candidate.frameQueryConvention };
        const numbers = value => typeof value === 'number' ? [value] : value && typeof value === 'object' ? Object.values(value).flatMap(numbers) : [];
        arithmetic.digitGrowth.normalized = arithmetic.digitGrowth.raw = 0;
        numbers([item.model, item.parameter]).forEach(arithmetic.binary64);
        const inputDigits = arithmetic.digitGrowth.normalized;
        arithmetic.digitGrowth.normalized = arithmetic.digitGrowth.raw = 0;
        const started = performance.now();
        let certificate, outcome;
        try {
            certificate = new candidate.FrameCandidates().produce(candidate.compileFrame(item.model, query));
            outcome = certificate.kind;
        } catch (error) { outcome = String(error); }
        const elapsedMs = performance.now() - started;
        const growth = { ...arithmetic.digitGrowth };
        let outputDigits = null, packetBytes = null;
        if (certificate) {
            const values = [certificate.motion, certificate.reactions, certificate.lower.flat(), certificate.diagonal,
                certificate.readouts, [certificate.loadWork]].flat();
            outputDigits = Math.max(...values.flatMap(value => [(value.n < 0n ? -value.n : value.n).toString().length, value.d.toString().length]));
            const packet = framePacket(item.model, query, certificate);
            packetBytes = packet.length;
            await writeFile(join(destination, `${cap}-${item.name}.packet`), packet);
        }
        rows.push({ cap, name: item.name, inputDigits, maxNormalizedDigits: growth.normalized,
            maxRawOperationDigits: growth.raw, outputDigits, packetBytes, elapsedMs, outcome });
    }
}
const report = { environment: { node: process.version, platform: process.platform, arch: process.arch },
    note: 'Single candidate measurements on this host, including first-call overhead. Not a WASM timing guarantee. Production cap unchanged.', rows };
await writeFile(join(destination, 'candidate-growth.json'), JSON.stringify(report, null, 2));
console.log(JSON.stringify(report, null, 2));
