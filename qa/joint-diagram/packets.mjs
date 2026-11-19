import { registerHooks } from 'node:module';
import { mkdir, writeFile } from 'node:fs/promises';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { example } = await import('../../web/engine.ts');
const { FrameCandidates, frameQueryConvention } = await import('../../web/frame-candidate.ts');
const { compileHingeFrame } = await import('../../web/frame-hinge-candidate.ts');
const { hingePacket } = await import('../../web/frame-hinge-packet.ts');
const { proposeSpringPacket } = await import('../../web/frame-spring-packet.ts');
const dir = '.data/joint-diagram/';
await mkdir(dir, { recursive: true });

for (const stiffness of [0, 2500, 5000]) {
    const model = example(stiffness ? 'semi-rigid' : 'hinge');
    if (stiffness) model.nodes[1].rotationStiffness = stiffness;
    model.supports = [model.supports[0], {id:'S2', member:'BC', t:1, kind:'fixed', angle:90}];
    for (const load of ['point','affine']) {
        model.loads = [{id:'L', member:'AB', kind:load === 'point' ? 'force' : 'distributed',
            t:load === 'point' ? 1 : 0, end:1, fx:0, fy:load === 'point' ? -10 : -4, mz:0, qEnd:4}];
        for (const member of ['AB','BC']) {
            const query = {...frameQueryConvention, member, parameter:0.5, cutSide:'left'};
            const filename = dir + [stiffness,load,member].join('-');
            if (stiffness) {
                const {packet, coordinates} = proposeSpringPacket(model, query, 96);
                await writeFile(filename + '.packet', packet);
                const tokens = new TextDecoder().decode(packet).split('\n');
                const start = tokens.length - 2*(coordinates**2 + coordinates);
                for (let i=0; i<coordinates**2; i++) tokens[start + 2*i] = '0';
                await writeFile(filename + '.reject', tokens.join('\n'));
                if (stiffness === 5000 && member === 'BC' && load === 'point') {
                    // Replace the source while retaining the old numerical proposal.
                    const edited = structuredClone(model);
                    edited.nodes[1].rotationStiffness = 1e8;
                    const changed = proposeSpringPacket(edited, query, 96);
                    const source = new TextDecoder().decode(changed.packet).split('\n').slice(0,start);
                    const previous = new TextDecoder().decode(packet).split('\n').slice(start);
                    await writeFile(dir + 'changed-source.reject', [...source,...previous].join('\n'));
                    edited.nodes[1].rotationStiffness = stiffness;
                    edited.nodes[2].y = 2;
                    await writeFile(dir + 'inclined-outside-cardinal.reject', proposeSpringPacket(edited,query,96).packet);
                }
            } else {
                const witness = new FrameCandidates().produce(compileHingeFrame(model, query));
                await writeFile(filename + '.packet', hingePacket(model, query, witness));
                witness.readouts[2].n += 1n;
                await writeFile(filename + '.reject', hingePacket(model, query, witness));
            }
        }
    }
}
