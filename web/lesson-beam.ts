/** Bounded teaching example. P > 0 acts downward; units are kN and m.
 * Formula readouts are tested against the frame engine. They are not individual
 * Lean certificates: the lesson links to the existing formal worked solutions.
 */
import type { Model } from './engine.js';

export interface BeamInputs { load: number; span: number; position: number; }
export const initialBeam: BeamInputs = { load: 20, span: 8, position: 0.5 };
export type SupportCase = 'pin-roller' | 'two-rollers' | 'three-rollers' | 'fixed-roller';

export function lessonBeam(inputs: BeamInputs = initialBeam, supports: SupportCase = 'pin-roller'): Model {
    const { load, span, position } = inputs;
    if (![load, span, position].every(Number.isFinite) || load < 5 || load > 50 || span < 4 || span > 12 || position < 0.1 || position > 0.9)
        throw Error('The lesson uses P = 5–50 kN, L = 4–12 m, and a/L = 0.1–0.9.');
    const model: Model = {
        nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: span, y: 0 }],
        members: [{ id: 'AB', a: 'A', b: 'B', EA: 2000000, EI: 20000 }],
        supports: [
            { id: 'S1', member: 'AB', t: 0, kind: supports === 'fixed-roller' ? 'fixed' : supports === 'pin-roller' ? 'pin' : 'roller', angle: 90 },
            { id: 'S2', member: 'AB', t: 1, kind: 'roller', angle: 90 },
        ],
        loads: [{ id: 'P1', label: 'P', member: 'AB', kind: 'force', t: position, end: 1, fx: 0, fy: -load, mz: 0, qEnd: 0 }],
    };
    if (supports === 'three-rollers')
        model.supports.push({ id: 'S3', member: 'AB', t: 0.5, kind: 'roller', angle: 90 });
    return model;
}

/** Right-hand shear at a concentrated force; moment is continuous there. */
export function beamValues(inputs: BeamInputs, section = 0.5) {
    lessonBeam(inputs);
    if (!Number.isFinite(section) || section < 0 || section > 1) throw Error('Section must lie on the span.');
    const { load: P, span: L, position } = inputs;
    const a = position * L, x = section * L;
    const left = P * (1 - position), right = P * position;
    const pastLoad = section >= position;
    return { a, x, left, right, normal: 0,
        shear: pastLoad ? -right : left,
        moment: left * x - (pastLoad ? P * (x - a) : 0),
        peak: P * a * (L - a) / L,
    };
}

/** Only the named activity changes workspace initialisation and storage. */
export function lessonContext(search: string): { model: Model; storageKey: string } | null {
    const params = new URLSearchParams(search);
    if (params.get('lesson') !== 'beam-basics') return null;
    const inputs = { ...initialBeam };
    for (const key of ['load', 'span', 'position'] as const) {
        if (params.has(key)) inputs[key] = Number(params.get(key));
    }
    let model: Model;
    try { model = lessonBeam(inputs); }
    catch { Object.assign(inputs, initialBeam); model = lessonBeam(inputs); }
    // Each starting example has its own resumable workspace. Refreshing never
    // discards edits; the workspace offers an explicit restart action instead.
    const exampleKey = [inputs.load, inputs.span, inputs.position].join(':');
    return { model, storageKey: `cv2011-model-lesson-beam:${exampleKey}` };
}
