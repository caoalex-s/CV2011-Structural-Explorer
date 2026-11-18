/** Source/witness packets for the native and compiled hinge checker. */
import { registerHooks } from 'node:module';
import { mkdir, writeFile } from 'node:fs/promises';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { example } = await import('../../web/engine.ts');
const { compileHingeFrame } = await import('../../web/frame-hinge-candidate.ts');
const { hingePacket } = await import('../../web/frame-hinge-packet.ts');
const { FrameCandidates, frameQueryConvention } = await import('../../web/frame-candidate.ts');
const output = '.data/hinge-packets';
await mkdir(output, { recursive: true });
const query = { ...frameQueryConvention, member: 'BC', parameter: 0, cutSide: 'right' };
async function save(name, model, witness) {
    await writeFile(output + '/' + name + '.packet', hingePacket(model, query, witness));
}
for (const name of ['hinge', 'mixed']) {
    const model = example(name);
    const witness = new FrameCandidates().produce(compileHingeFrame(model, query));
    await save('1_' + name, model, witness);
    const wrong = structuredClone(witness);
    wrong.readouts[2].n += 1n;
    await save('0_' + name + '_wrong_moment', model, wrong);
}
const mechanism = example('hinge');
mechanism.supports.pop();
await save('1_mechanism', mechanism, new FrameCandidates().produce(compileHingeFrame(mechanism, query)));
