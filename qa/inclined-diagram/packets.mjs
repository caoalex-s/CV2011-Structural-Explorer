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
for (const h of [2,3]) {
    for (const reverse of [false,true]) {
        const model = example('cantilever');
        model.nodes[1].x = 4;
        model.nodes[1].y = h;
        if (reverse) [model.members[0].a,model.members[0].b] = ['B','A'];
        model.supports[0].t = reverse ? 1 : 0;
        model.loads[0].t = reverse ? 0 : 1;
        model.loads[0].fy = -5;
        model.loads.push({id:'affine',member:'AB',kind:'distributed',t:0,end:1,fx:0,fy:reverse?6:-6,qEnd:reverse?-6:6,mz:0});
        const query = {...frameQueryConvention, member:'AB',parameter:.5,cutSide:'left'};
        const {packet,coordinates} = proposeInclinedPacket(model,query,96);
        const name = dir + 'h' + h + (reverse ? '-reverse' : '-forward');
        await writeFile(name + '.packet',packet);
        const tokens = new TextDecoder().decode(packet).split('\n');
        const offset = tokens.length - 2*(coordinates**2+coordinates);
        for (let i=0;i<coordinates**2;i++) tokens[offset+2*i]='0';
        await writeFile(name + '.reject',tokens.join('\n'));
    }
}
