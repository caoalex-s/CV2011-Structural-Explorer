/** Public example derivations checked during deployment, without a live service. */
import type { Model } from './engine.js';
import type { WorkedResponse } from './worked.js';

export interface PublishedExample {
    name: string;
    model: Model;
    solutions: { section: number; response: WorkedResponse }[];
}
export interface PublishedLibrary {
    schemaVersion: 1;
    examples: PublishedExample[];
}

/** Ignore object property order only. Preserve every model value and array order:
 * edits to loads, supports, stiffness, joints, or node labels invalidate reuse. */
function modelSignature(value: unknown): string {
    if (Array.isArray(value)) return `[${value.map(modelSignature).join(',')}]`;
    if (value !== null && typeof value === 'object') {
        const entries = Object.entries(value).sort(([left], [right]) => left.localeCompare(right));
        return `{${entries.map(([key, item]) => `${JSON.stringify(key)}:${modelSignature(item)}`).join(',')}}`;
    }
    return JSON.stringify(value);
}

export function findPublishedExample(model: Model, library: PublishedLibrary): PublishedExample | undefined {
    // Labels are display metadata. All mechanics, ordering, and IDs still agree.
    const mechanics = (candidate: Model) => ({ ...candidate, loads: candidate.loads.map(({ label, ...load }) => load) });
    const signature = modelSignature(mechanics(model));
    return library.examples.find(example => modelSignature(mechanics(example.model)) === signature);
}

export function publishedSolution(example: PublishedExample, section: number): WorkedResponse | undefined {
    // Never display a nearby section's certificate as the current solution.
    return example.solutions.find(solution => solution.section === section && solution.response.proof.status === 'checked')?.response;
}

let libraryRequest: Promise<PublishedLibrary> | undefined;
export async function loadPublishedLibrary(): Promise<PublishedLibrary> {
    if (!libraryRequest) {
        libraryRequest = (async () => {
            const result = await fetch(new URL('./worked-examples.json', import.meta.url), { signal: AbortSignal.timeout(15000) });
            if (!result.ok) throw Error('The published example solutions could not be loaded. Try again or open the local workspace.');
            const library = await result.json() as PublishedLibrary;
            if (library.schemaVersion !== 1 || !Array.isArray(library.examples)) throw Error('The published solutions need an update. Reload this page.');
            return library;
        })().catch(failure => {
            libraryRequest = undefined;
            throw failure;
        });
    }
    return libraryRequest;
}
