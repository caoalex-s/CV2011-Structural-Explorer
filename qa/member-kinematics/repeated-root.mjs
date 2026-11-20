import { registerHooks } from 'node:module';
import { writeFile } from 'node:fs/promises';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { example } = await import('../../web/engine.ts');
const { proposeInclinedPacket } = await import('../../web/frame-interval-packet.ts');
const { frameQueryConvention } = await import('../../web/frame-candidate.ts');
const { compareDeformationReport, parseDeformationReport } = await import('./member-diagram-deformation-audit.mjs');
const { repeatedDisplacementRoot } = await import('./member-diagram-deformation-reference.mjs');
const path = '.data/inclined-diagram/repeated-root.packet';
if (process.argv[2] === 'verify') {
    const { readFile } = await import('node:fs/promises');
    const report = parseDeformationReport(await readFile(path + '.report', 'utf8'), 'AB');
    compareDeformationReport(report, repeatedDisplacementRoot());
} else {
    const model = example('cantilever');
    model.nodes[1].x = 4;
    model.members[0].EI = 20000;
    const force = model.loads[0];
    force.fy = -16;
    model.loads.push({ ...force, id: 'applied-couple', kind: 'moment', mz: 20, fy: 0 },
        { ...force, id: 'uniform-upward', kind: 'distributed', t: 0, fy: 6, qEnd: 6 });
    const query = { ...frameQueryConvention, member: 'AB', parameter: 0.5, cutSide: 'left' };
    await writeFile(path, proposeInclinedPacket(model, query, 96).packet);
}
