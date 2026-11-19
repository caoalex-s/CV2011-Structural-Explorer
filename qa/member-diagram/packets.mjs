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
const output = process.argv[2] ?? '.data/diagram';
await mkdir(output, { recursive: true });
const selected = (member, parameter = 0.5, cutSide = 'left') => ({ member, parameter, cutSide, ...frameQueryConvention });
const make = (source, query) => new FrameCandidates().produce(compileFrame(source, query));
const save = (name, source, query, certificate = make(source, query)) =>
    writeFile(join(output, name + '.packet'), framePacket(source, query, certificate));
const portal = example('frame');
portal.loads[0].fy = -6;
portal.loads[0].qEnd = 6;
await save('portal', portal, selected('BC'));
const result = make(portal, selected('BC'));
result.motion[0] = one;
await writeFile(join(output, 'different-motion.reject'), framePacket(portal, selected('BC'), result));
