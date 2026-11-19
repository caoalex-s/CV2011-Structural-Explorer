import { registerHooks } from 'node:module';
import { mkdir, writeFile } from 'node:fs/promises';
registerHooks({resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
}});
const { example } = await import('../../web/engine.ts');
const { frameQueryConvention } = await import('../../web/frame-candidate.ts');
const { proposeSpringPacket } = await import('../../web/frame-spring-packet.ts');
const dir = '.data/frame-spring';
await mkdir(dir, {recursive:true});
for (const stiffness of [10000, 20000]) {
    for (const rise of [0, 2]) {
        const model = example('semi-rigid');
        model.nodes[1].rotationStiffness = stiffness;
        model.nodes[2].y = rise;
        model.loads = [{ id: 'tip', member: 'BC', kind: 'moment', t: 1, end: 1, fx: 0, fy: 0, mz: 10, qEnd: 0 }];
        const query = { ...frameQueryConvention, member: 'BC', parameter: 0, cutSide: 'right' };
        const { packet, coordinates } = proposeSpringPacket(model, query, 96);
        const file = dir + '/' + stiffness + '-' + rise;
        await writeFile(file + '.packet', packet);
        const tokens = new TextDecoder().decode(packet).split('\n');
        const start = tokens.length - 2 * (coordinates * coordinates + coordinates);
        for (let i = 0; i < coordinates * coordinates; i++) tokens[start + 2 * i] = '0';
        await writeFile(file + '.reject', tokens.join('\n'));
    }
}
