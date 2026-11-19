import { registerHooks } from 'node:module';
import { mkdir, writeFile } from 'node:fs/promises';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { example } = await import('../../web/engine.ts');
const { frameQueryConvention } = await import('../../web/frame-candidate.ts');
const { proposeInclinedPacket } = await import('../../web/frame-interval-packet.ts');
const dir = '.data/inclined-diagram/';
await mkdir(dir, {recursive:true});
const { proposeSpringPacket } = await import('../../web/frame-spring-packet.ts');
const { proposeInclinedReleasePacket } = await import('../../web/frame-inclined-release-packet.ts');

async function save(name, model, member, proposer) {
    const query = {...frameQueryConvention, member, parameter: 0.5, cutSide: 'left'};
    const { packet, coordinates } = proposer(model, query, 96);
    await writeFile(dir + name + '.packet', packet);
    const tokens = new TextDecoder().decode(packet).split('\n');
    const inverseStart = tokens.length - 2 * (coordinates ** 2 + coordinates);
    for (let i = 0; i < coordinates ** 2; i++) {
        tokens[inverseStart + 2*i] = '0';
        tokens[inverseStart + 2*i + 1] = '1';
    }
    await writeFile(dir + name + '.reject', tokens.join('\n'));
}
for (const h of [2, 3]) {
    for (const reverse of [false, true]) {
        const model = example('cantilever');
        model.nodes[1].x = 4;
        model.nodes[1].y = h;
        if (reverse) [model.members[0].a, model.members[0].b] = ['B', 'A'];
        model.supports[0].t = reverse ? 1 : 0;
        model.loads[0].t = reverse ? 0 : 1;
        model.loads[0].fy = -5;
        model.loads.push({ id: 'affine', member: 'AB', kind: 'distributed', t: 0, end: 1,
            fx: 0, fy: reverse ? 6 : -6, qEnd: reverse ? -6 : 6, mz: 0 });
        await save('h' + h + (reverse ? '-reverse' : '-forward'), model, 'AB', proposeInclinedPacket);
    }
}
const jump = example('cantilever');
jump.nodes[1].x = 4;
jump.nodes[1].y = 2;
jump.loads[0].t = 0.5;
jump.loads[0].fy = -10;
jump.loads.push({ ...jump.loads[0], id: 'couple', kind: 'moment', t: 0.75, fy: 0, mz: 6 });
await save('jump', jump, 'AB', proposeInclinedPacket);

const hinge = example('hinge');
hinge.nodes[2].y = 2;
hinge.supports[1].kind = 'pin';
hinge.loads[0].fy = -10;
await save('release', hinge, 'BC', proposeInclinedReleasePacket);
for (const reverse of [false, true]) {
    const spring = example('semi-rigid');
    spring.nodes[2].y = 2;
    spring.nodes[1].rotationStiffness = 5000;
    if (reverse) [spring.members[1].a, spring.members[1].b] = ['C', 'B'];
    spring.loads[0].t = reverse ? 0 : 1;
    spring.loads[0].fy = -5;
    spring.loads.push({ ...spring.loads[0], id: 'couple', kind: 'moment', fy: 0, mz: 30 });
    await save(reverse ? 'spring-reverse' : 'spring-forward', spring, 'BC', proposeSpringPacket);
}