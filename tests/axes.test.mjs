import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
import { example } from '../web/engine.ts';

registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { memberBasis, workspaceConventions } = await import('../web/axes.ts');

test('local axes follow the selected member including reversed and inclined members', () => {
    const model = example();
    const member = model.members[0];
    const start = model.nodes.find(node => node.id === member.a);
    const end = model.nodes.find(node => node.id === member.b);
    Object.assign(start, { x: 1, y: 2 });
    Object.assign(end, { x: 4, y: 6 });
    assert.equal(memberBasis(model, member.id).cosine, 0.6);
    assert.equal(memberBasis(model, member.id).sine, 0.8);
    [member.a, member.b] = [member.b, member.a];
    assert.equal(memberBasis(model, member.id).cosine, -0.6);
    assert.equal(memberBasis(model, member.id).sine, -0.8);
    const convention = workspaceConventions(model, member.id);
    const formulas = [...convention.matchAll(/<annotation[^>]*>([^<]+)<\/annotation>/g)].map(match => match[1]);
    assert.deepEqual(formulas, ['N', '+x', 'V', '-y', 'M', 'u_y', '\\theta', 'x', 'y', '90^\\circ', 'x']);
    assert.doesNotMatch(convention, /math-error/);
    assert.equal(memberBasis(model, 'missing'), undefined);
});
