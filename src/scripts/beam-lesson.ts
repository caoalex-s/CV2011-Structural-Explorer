import { analyse } from '../../web/engine.js';
import { initialBeam, lessonBeam } from '../../web/lesson-beam.js';
import type { BeamInputs, SupportCase } from '../../web/lesson-beam.js';
import { beamDrawing, reactionEquations, sectionEquations } from '../../web/lesson-view.js';
import { createLearningSession } from '../../web/learning-session.js';
import { element as $, escapeHtml } from '../../web/ui.js';
import questions from '../data/questions.json' with { type: 'json' };

let inputs: BeamInputs = { ...initialBeam }, section = 0.5;
const base = document.body.dataset.base || '/';
let toastTimer: ReturnType<typeof setTimeout>;
function notify(message: string) {
    $('toast').textContent = message;
    $('toast').classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => $('toast').classList.remove('show'), 5000);
}
const session = createLearningSession({ notify, onConnectionChange: () => session.updateStatus() });
void session.connect();
session.updateStatus();

function context(step: string, revealed = false) {
    return { model: lessonBeam(inputs), section, step, side: $<HTMLSelectElement>('lesson-moment-side').value,
        hintUsed: false, solutionRevealed: revealed };
}

function renderBeam() {
    const compression = $<HTMLSelectElement>('lesson-moment-side').value === 'compression';
    $('beam-drawing').innerHTML = beamDrawing(inputs, section, compression);
    $('reaction-equations').innerHTML = reactionEquations(inputs);
    $('section-equations').innerHTML = sectionEquations(inputs, section);
    $('load-value').textContent = `${inputs.load} kN`;
    $('span-value').textContent = `${inputs.span} m`;
    $('position-value').textContent = inputs.position.toFixed(2);
    $('section-value').textContent = section.toFixed(2);
    const parameters = new URLSearchParams({ lesson: 'beam-basics', load: String(inputs.load), span: String(inputs.span), position: String(inputs.position) });
    $<HTMLAnchorElement>('explore-current').href = `${base}?${parameters}#sandbox`;
}
for (const [id, key] of [['beam-load', 'load'], ['beam-span', 'span'], ['beam-position', 'position']] as const) {
    $<HTMLInputElement>(id).addEventListener('input', event => {
        inputs[key] = Number((event.target as HTMLInputElement).value);
        renderBeam();
    });
}
$('lesson-section').addEventListener('input', event => {
    section = Number((event.target as HTMLInputElement).value);
    renderBeam();
});
$('lesson-moment-side').addEventListener('change', renderBeam);
$('reset-beam').onclick = () => {
    inputs = { ...initialBeam }; section = 0.5;
    $<HTMLInputElement>('beam-load').value = String(inputs.load);
    $<HTMLInputElement>('beam-span').value = String(inputs.span);
    $<HTMLInputElement>('beam-position').value = String(inputs.position);
    $<HTMLInputElement>('lesson-section').value = String(section);
    renderBeam();
};

// Capture on the persistent SVG element: replacing its child paths during a
// drag must not lose pointer capture. Sliders provide keyboard equivalents.
const drawing = $('beam-drawing') as unknown as SVGSVGElement;
let dragging: number | null = null;
function moveForce(event: PointerEvent) {
    const transform = drawing.getScreenCTM();
    if (!transform) return;
    const point = new DOMPoint(event.clientX, event.clientY).matrixTransform(transform.inverse());
    inputs.position = Math.max(0.1, Math.min(0.9, Math.round((point.x - 100) / 560 * 20) / 20));
    $<HTMLInputElement>('beam-position').value = String(inputs.position);
    renderBeam();
}
drawing.addEventListener('pointerdown', event => {
    if (!(event.target instanceof Element) || !event.target.closest('[data-drag-load]')) return;
    event.preventDefault(); dragging = event.pointerId;
    drawing.setPointerCapture(event.pointerId); moveForce(event);
});
drawing.addEventListener('pointermove', event => { if (dragging === event.pointerId) moveForce(event); });
for (const name of ['pointerup', 'pointercancel', 'lostpointercapture']) {
    drawing.addEventListener(name, () => { dragging = null; });
}

const supportMessages: Record<SupportCase, string> = {
    'pin-roller': 'Stable and statically determinate. The pin and separated roller prevent both translations and rigid-body rotation.',
    'two-rollers': 'Unstable: partial constraints. Only two reaction components are available, and horizontal translation is free.',
    'three-rollers': 'Unstable: improper constraints. All three reactions are parallel, leaving horizontal translation free despite the reaction count.',
    'fixed-roller': 'Stable and statically indeterminate to degree one. Four reaction components require a compatibility condition in addition to the three equilibrium equations.',
};
$('support-case').addEventListener('change', () => {
    const supports = $<HTMLSelectElement>('support-case').value as SupportCase;
    const result = analyse(lessonBeam(initialBeam, supports));
    $('support-drawing').innerHTML = beamDrawing(initialBeam, 0.5, false, supports, false);
    $('support-result').textContent = ['stable', 'unstable'].includes(result.status) ? supportMessages[supports] : result.message;
});

for (const form of document.querySelectorAll<HTMLFormElement>('[data-question]')) {
    const question = questions.find(item => item.id === form.dataset.question)!;
    let feedbackSeen = false;
    form.addEventListener('submit', async event => {
        event.preventDefault();
        const answer = String(new FormData(form).get(question.id));
        const feedback = form.querySelector<HTMLElement>('.feedback')!;
        const submit = form.querySelector<HTMLButtonElement>('button')!;
        const choice = question.choices.find(item => item.id === answer);
        if (!choice) return;
        submit.disabled = true;
        feedback.hidden = false;
        feedback.textContent = `${answer === question.correct ? 'Correct.' : 'Review the free body.'} ${question.explanation}`;
        try {
            const attemptContext = context(question.id, feedbackSeen);
            feedbackSeen = true;
            if (question.id === 'concept_parallel_restraints_v1')
                attemptContext.model = lessonBeam(initialBeam, 'three-rollers');
            const attempt = await session.record(attemptContext, 'submit', answer, 'choice');
            feedback.insertAdjacentHTML('beforeend', `<span class="small">${escapeHtml(attempt.synced ? 'Recorded by the connected service.' : 'Saved on this device. Upload through Learning insights after connecting.')}</span>`);
        } catch {
            notify('The feedback is available, but browser storage could not save this attempt.');
        } finally { submit.disabled = false; }
    });
}
for (const details of document.querySelectorAll<HTMLDetailsElement>('[data-reveal]')) {
    details.addEventListener('toggle', () => {
        if (details.open && !printing) void session.record(context(details.dataset.reveal!, true), 'reveal', '', '').catch(() => notify('The solution reveal could not be saved.'));
    });
}

// Print includes all derivations. Restore disclosure state without recording
// automatic print expansion as student solution-reveal events.
let printing = false;
let closedBeforePrint: HTMLDetailsElement[] = [];
window.addEventListener('beforeprint', () => {
    printing = true;
    closedBeforePrint = [...document.querySelectorAll<HTMLDetailsElement>('details:not([open])')];
    closedBeforePrint.forEach(details => { details.open = true; });
});
window.addEventListener('afterprint', () => {
    closedBeforePrint.forEach(details => { details.open = false; });
    setTimeout(() => { printing = false; }, 0);
});
$('print-lesson').onclick = () => window.print();
fetch(`${base}verification.json`).then(response => {
    if (!response.ok) throw Error('No receipt');
    return response.json();
}).then(receipt => {
    $('lesson-proof-status').textContent = receipt.lean === 'checked'
        ? 'Published library: Lean checked. Scope: scaled reaction-equilibrium identities and plotting-side inversion.'
        : 'Proof source available. No successful Lean check is recorded in this build.';
}).catch(() => { $('lesson-proof-status').textContent = 'Proof source available. The check status could not be loaded.'; });
renderBeam();
