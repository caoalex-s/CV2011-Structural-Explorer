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
    model.nodes.find(n => n.id === 'C').y = 2;
    model.supports.find(support => support.kind === 'roller').angle = 45;
    model.loads.find(load => load.kind === 'force').fy = -10;
    const span = model.members.find(m => m.id === 'BC');
    if (reversed) {
        [span.a, span.b] = [span.b, span.a];
        for (const item of [...model.supports, ...model.loads].filter(i => i.member === span.id)) item.t = 1-item.t;
    }
    const query = { ...frameQueryConvention, member: span.id, parameter: reversed ? 1 : 0, cutSide: reversed ? 'left' : 'right' };
    const { packet } = proposeInclinedReleasePacket(model, query, 96);
    const name = reversed ? 'reverse' : 'forward';
    await writeFile(dir + '/' + name + '.packet', packet);
    model.loads.push({ id: 'end-couple', kind: 'moment', member: span.id, t: query.parameter,
        end: 1, fx: 0, fy: 0, mz: 10, qEnd: 0 });
    const loaded = proposeInclinedReleasePacket(model, query, 96);
    await writeFile(dir + '/' + name + '-couple.packet', loaded.packet);
    // The final n canonical fractions are the proposed amplitudes. Perturbing
    // the inverse to zero destroys the contraction even for an unloaded model.
    const tokens = new TextDecoder().decode(loaded.packet).split('\n');
    const n = loaded.coordinates;
    const offset = tokens.length - 2 * (n*n + n);
    for (let i = 0; i < n*n; i++) { tokens[offset+2*i] = '0'; tokens[offset+2*i+1] = '1'; }
    await writeFile(dir + '/' + name + '.reject', tokens.join('\n'));
}
