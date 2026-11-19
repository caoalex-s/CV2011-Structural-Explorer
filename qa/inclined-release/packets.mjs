import { registerHooks } from 'node:module';
import { mkdir, writeFile } from 'node:fs/promises';
registerHooks({resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
}});
const { example } = await import('../../web/engine.ts');
const { frameQueryConvention } = await import('../../web/frame-candidate.ts');
const { proposeInclinedReleasePacket } = await import('../../web/frame-inclined-release-packet.ts');
const dir = '.data/inclined-release';
await mkdir(dir, {recursive:true});
for (const reversed of [false,true]) {
    const model = example('hinge');
    model.nodes.find(n => n.id === 'C').y = 3;
    const span = model.members.find(m => m.id === 'BC');
    if (reversed) {
        [span.a, span.b] = [span.b, span.a];
        for (const item of [...model.supports, ...model.loads].filter(i => i.member === span.id)) item.t = 1-item.t;
    }
    const query = { ...frameQueryConvention, member: span.id, parameter: reversed ? 1 : 0, cutSide: reversed ? 'left' : 'right' };
    const { packet } = proposeInclinedReleasePacket(model, query, 96);
    await writeFile(dir + '/' + (reversed ? 'reverse' : 'forward') + '.packet', packet);
}
