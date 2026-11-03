import test from 'node:test';
import assert from 'node:assert/strict';
import { example } from '../web/engine.ts';
import { findPublishedExample, publishedSolution } from '../web/published-worked.ts';

const model = example('beam');
const published = { name: 'Simply supported beam', model, solutions: [
    { section: 0.5, response: { proof: { status: 'checked' }, section: '4' } },
    { section: 0.25, response: { proof: { status: 'not_run' }, section: '2' } },
] };
const library = { schemaVersion: 1, examples: [published] };

test('published solutions tolerate JSON property order without changing the drawing', () => {
    const reordered = Object.fromEntries(Object.entries(structuredClone(model)).reverse());
    assert.equal(findPublishedExample(reordered, library), published);
});

test('a model edit cannot inherit a published Lean certificate', () => {
    const edits = [
        candidate => { candidate.loads[0].fy -= 1; },
        candidate => { candidate.loads[0].t += 0.001; },
        candidate => { candidate.supports[0].t += 0.01; },
        candidate => { candidate.members[0].EI *= 2; },
        candidate => { candidate.nodes[0].x += 0.1; },
        candidate => { candidate.nodes[0].joint = 'pinned'; },
        candidate => { candidate.nodes.reverse(); },
    ];
    for (const edit of edits) {
        const candidate = structuredClone(model);
        edit(candidate);
        assert.equal(findPublishedExample(candidate, library), undefined);
    }
});

test('a section must have its own checked response', () => {
    assert.equal(publishedSolution(published, 0.5).section, '4');
    assert.equal(publishedSolution(published, 0.501), undefined);
    assert.equal(publishedSolution(published, 0.25), undefined);
});
