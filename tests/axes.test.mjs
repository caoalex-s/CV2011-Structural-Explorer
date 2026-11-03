import test from 'node:test';
import assert from 'node:assert/strict';
import { memberBasis, workspaceConventions } from '../web/axes.ts';
import { example } from '../web/engine.ts';

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
    assert.match(workspaceConventions(model, member.id), /V along −y/);
    assert.match(workspaceConventions(model, member.id), /Readouts: \+v upward · \+θ ↺/);
    assert.equal(memberBasis(model, 'missing'), undefined);
});
