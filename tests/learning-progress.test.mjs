import test from 'node:test';
import assert from 'node:assert/strict';
import { conceptWasAssisted, selectSubmissions } from '../web/learning-progress.ts';

const record = (id, changes = {}) => ({
    id: String(id), timestamp: `2026-11-04T00:00:0${id}Z`, courseId: 'PILOT-A',
    event: 'submit', step: 'concept_reaction_trend_v1', model: {}, section: 0.5,
    hintUsed: false, solutionRevealed: false, ...changes,
});

test('concept exposure survives reconstruction from saved records and includes related derivations', () => {
    const history = JSON.parse(JSON.stringify([record(1, {event: 'reveal', step: 'reaction_left'})]));
    assert.equal(conceptWasAssisted(history, 'PILOT-A', 'concept_reaction_trend_v1'), true);
    assert.equal(conceptWasAssisted(history, 'PILOT-B', 'concept_reaction_trend_v1'), false);
    assert.equal(conceptWasAssisted(history, 'PILOT-A', 'concept_point_force_jump_v1'), false);
    assert.equal(conceptWasAssisted([record(1)], 'PILOT-A', 'concept_reaction_trend_v1'), true);
});

test('first recorded answers exclude assisted first submissions and never promote a retry', () => {
    const history = [record(3, {solutionRevealed: true}), record(1),
        record(2, {courseId: 'PILOT-B', solutionRevealed: true})];
    assert.deepEqual(selectSubmissions(history, 'first').map(row => row.attempt.id), ['1']);
    assert.deepEqual(selectSubmissions(history, 'retry').map(row => row.attempt.id), ['3']);
    assert.deepEqual(selectSubmissions(history, 'assisted').map(row => row.attempt.id), ['2', '3']);
    assert.equal(selectSubmissions(history, 'all').length, 3);
});

test('concepts keep their attempt sequence across slider changes; numeric problems keep separate cuts', () => {
    const history = [record(1), record(2, {section: 0.75}),
        record(3, {step: 'moment'}), record(4, {step: 'moment', section: 0.75})];
    assert.deepEqual(selectSubmissions(history, 'all').map(row => row.ordinal), [1, 2, 1, 1]);
});
