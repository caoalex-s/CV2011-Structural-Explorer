/** Interpret recorded tool usage without claiming to measure independent mastery. */
import type { Attempt } from './learning-session.js';

const relatedReveals: Record<string, string[]> = {
    concept_parallel_restraints_v1: ['supports'],
    concept_reaction_trend_v1: ['reaction_left'],
    concept_point_force_jump_v1: ['moment', 'cut'],
};

export function conceptWasAssisted(records: Attempt[], courseId: string, step: string): boolean {
    const relevantSteps = [step, ...(relatedReveals[step] || [])];
    return records.some(record =>
        (record.courseId === courseId || record.courseId === 'local-unassigned') &&
        relevantSteps.includes(record.step) &&
        (record.event === 'reveal' || (record.event === 'submit' && record.step === step)),
    );
}

export type SubmissionGroup = 'all' | 'first' | 'retry' | 'assisted';
export function submissionHistory(records: Attempt[]) {
    const counts = new Map<string, number>();
    return records.filter(record => record.event === 'submit')
        .sort((a, b) => a.timestamp.localeCompare(b.timestamp) || a.id.localeCompare(b.id))
        .map(attempt => {
            // A concept question has one identity across slider settings. Numeric
            // work is grouped by model and cut because those define its answer.
            const problem = attempt.step.startsWith('concept_') ? '' : JSON.stringify([attempt.model, attempt.section]);
            const key = JSON.stringify([attempt.courseId, attempt.step, problem]);
            const ordinal = (counts.get(key) || 0) + 1;
            counts.set(key, ordinal);
            return { attempt, ordinal, assisted: !!(attempt.hintUsed || attempt.solutionRevealed) };
        });
}

export function selectSubmissions(records: Attempt[], group: SubmissionGroup) {
    return submissionHistory(records).filter(row => group === 'all' ||
        (group === 'first' && row.ordinal === 1 && !row.assisted) ||
        (group === 'retry' && row.ordinal > 1) ||
        (group === 'assisted' && row.assisted));
}
