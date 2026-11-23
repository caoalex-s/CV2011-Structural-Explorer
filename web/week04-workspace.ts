import type { Drawing } from './ideal-truss.js';
import { createLearningSession } from './learning-session.js';
import { isolateForCheck } from './truss-check.js';
import { element as el, escapeHtml } from './ui.js';
import { diagram } from './week04-figures.js';
import { solution } from './week04-solution.js';
import { checkedSection, crossed, invalidateSection, members, type Query } from './week04-section.js';
document.body.classList.add('truss-workspace');
document.querySelector('.topbar nav')!.innerHTML = '<a href="./">Frame workspace</a> <a href="?exercise=ideal-planar-truss">Ideal planar truss</a>';
document.querySelector('.header-actions')!.innerHTML = '<button id="replay">Local replay</button> <button id="settings-button">Session</button> <button id="instructor">Learning insights</button>';
const fixture: Drawing = await (await fetch('./week04-section-truss.json')).json();
el('workspace').innerHTML = `<h1>Truss forces by the method of sections</h1>
<p>Week 04 · Example 1. Find the axial forces in BC, GC and GF. The lecture load of 1000 N acts downwards at A (P = 1 kN).</p>
<section class="panel"><div id="section-figure"></div><div class="section-controls">
<label>Vertical cut at x (m) <select id="section-cut"><option>1</option><option selected>3</option><option>5</option></select></label>
<label>Retained side <select id="section-side"><option value="left">Left</option><option value="right">Right</option></select></label>
<label>Moment centre <select id="section-centre">${fixture.joints.map(j => '<option' + (j.id === 'G' ? ' selected' : '') + '>' + j.id + '</option>').join('')}</select></label>
<label>P at A (kN, positive downwards) <input id="section-load" type="number" min="-1000" max="1000" step="1" value="1"></label></div><p id="section-selection"></p></section>
<section class="panel"><h2>Predict the force in each cut member</h2><div class="section-controls">${members.map(m => `<label>${m} <select id="predict-${m}"><option value="">Choose</option><option value="T">Tension</option><option value="C">Compression</option><option value="zero">Zero force</option></select></label>`).join('')}</div>
<button id="record-section">Record prediction</button> <button id="reveal-section" disabled>Reveal worked solution</button><p id="section-check" role="status"></p></section>
<section class="panel" id="section-response" hidden></section><section class="panel" id="history" hidden></section><section class="panel" id="insights-panel" hidden></section>`;
const field = (id: string) => el<HTMLInputElement | HTMLSelectElement>(id);
const button = (id: string) => el<HTMLButtonElement>(id);
const prediction = () => Object.fromEntries(members.map(m => [m, field('predict-' + m).value]));
const query = (): Query => ({ cut: Number(field('section-cut').value), side: field('section-side').value as Query['side'], centre: field('section-centre').value });
const clock = () => performance.timeOrigin + performance.now();
const session = createLearningSession({ exercise: 'week04_sections', notify: msg => { el('section-check').textContent = msg; }, onConnectionChange: () => session.updateStatus() });
session.updateStatus();
let drawing = structuredClone(fixture), revision = 0, started = clock(), pending: Promise<unknown> = Promise.resolve();
let recorded = false;
function clearResult() {
    revision++;
    invalidateSection();
    recorded = false;
    el('section-response').hidden = true;
    el('section-response').replaceChildren();
    el('section-check').textContent = '';
    button('reveal-section').disabled = true;
}
function refresh() {
    clearResult();
    started = clock();
    const input = el<HTMLInputElement>('section-load');
    drawing = structuredClone(fixture);
    const valid = input.value !== '' && input.validity.valid;
    if (valid)
        drawing.joints.find(j => j.id === 'A')!.fy = -input.valueAsNumber;
    const q = query(), crossings = crossed(drawing, q.cut);
    el('section-figure').innerHTML = valid ? diagram(drawing, q) : '';
    const target = valid && crossings.join(',') === members.join(',');
    el('section-selection').textContent = valid ? 'The cut passes through ' + crossings.join(', ') + '.' + (target ? '' : ' Select the cut through BC, GC and GF.') : 'Enter an integer load from −1000 to 1000 kN.';
    for (const m of members) {
        field('predict-' + m).value = '';
        field('predict-' + m).disabled = !target;
    }
    button('record-section').disabled = true;
}
function predictionChanged() {
    clearResult();
    button('record-section').disabled = !Object.values(prediction()).every(Boolean);
}
for (const id of ['section-cut', 'section-side', 'section-centre', 'section-load'])
    field(id).oninput = refresh;
for (const m of members)
    field('predict-' + m).oninput = predictionChanged;
const history = () => session.sectionEvents().filter(a => JSON.stringify(a.model) === JSON.stringify(drawing) && a.section === query().cut && a.side === query().side && JSON.parse(a.answer).centre === query().centre);
function log(event: string, assisted: boolean, elapsedMs: number) {
    const q = query();
    const context = { model: drawing, section: q.cut, side: q.side, step: 'week04_sections', hintUsed: false, solutionRevealed: assisted };
    const answer = JSON.stringify({ ...q, prediction: prediction(), elapsedMs });
    pending = session.record(context, event, answer, 'kN', pending);
}
button('record-section').onclick = () => {
    clearResult();
    const previous = history();
    log(previous.length ? 'retry' : 'first_prediction', previous.some(a => a.event === 'reveal'), clock() - started);
    recorded = true;
    button('reveal-section').disabled = false;
    el('section-check').textContent = 'Prediction recorded. Compare it with the section equilibrium.';
};
const resumeKey = 'cv2011-week04-resume';
async function reveal(began = clock(), resumed = false) {
    if (!recorded)
        return;
    const current = revision;
    button('reveal-section').disabled = true;
    el('section-check').textContent = 'Checking the drawing and section equilibrium…';
    try {
        if (!crossOriginIsolated) {
            if (resumed)
                throw Error('Browser isolation did not start.');
            await Promise.all([isolateForCheck(), pending]);
            if (revision !== current)
                return;
            sessionStorage.setItem(resumeKey, JSON.stringify({ q: query(), p: field('section-load').value, prediction: prediction(), connected: session.connected, courseId: session.courseId, began, started }));
            location.reload();
            return;
        }
        const q = query(), result = await checkedSection(drawing, q);
        if (current !== revision || !result)
            return;
        const response = el('section-response');
        response.innerHTML = solution(drawing, q, result.answer) + '<p id="section-comparison"></p><details><summary>Local check receipt</summary><pre id="section-receipt"></pre></details>';
        const correct = result.answer.terms.slice(0, 3).filter(t => prediction()[t.name] === (t.component > 0 ? 'T' : t.component < 0 ? 'C' : 'zero')).length;
        el('section-comparison').textContent = correct + ' of your 3 predictions agree with the checked forces.';
        response.hidden = false;
        await new Promise<void>(resolve => requestAnimationFrame(() => resolve()));
        if (current !== revision)
            return;
        result.receipt.elapsedMs = clock() - began;
        el('section-receipt').textContent = JSON.stringify(result.receipt, null, 2);
        el('section-check').textContent = 'Compiled Lean checked the cut coefficients and substitutions from this drawing. Time to worked answer ' + (result.receipt.elapsedMs / 1000).toFixed(2) + ' s.';
        log('reveal', true, result.receipt.elapsedMs);
    }
    catch (error) {
        if (current === revision) {
            el('section-check').textContent = String(error);
            button('reveal-section').disabled = false;
        }
    }
}
button('reveal-section').onclick = () => void reveal();
el('replay').onclick = async () => {
    await pending;
    el('history').innerHTML = '<h2>Local replay</h2>' + session.sectionEvents().map(a => '<details><summary>' + escapeHtml(a.event.replaceAll('_', ' ')) + ' · ' + escapeHtml(a.timestamp) + '</summary><pre>' + escapeHtml(a.answer) + '</pre></details>').join('');
    el('history').hidden = false;
    el('history').scrollIntoView();
};
el('instructor').onclick = async () => { await pending; el('insights-panel').hidden = false; await session.renderInsights(); el('insights-panel').scrollIntoView(); };
refresh();
type PendingReveal = {
    q: Query; p: string; prediction: Record<string,string>;
    connected: boolean; courseId: string; began: number; started: number;
};
function takePendingReveal(): PendingReveal | undefined {
    const saved = sessionStorage.getItem(resumeKey);
    sessionStorage.removeItem(resumeKey);
    if (!saved) return;
    try {
        const state = JSON.parse(saved) as PendingReveal;
        if ([1,3,5].includes(state.q.cut) && ['left','right'].includes(state.q.side) &&
            fixture.joints.some(j => j.id === state.q.centre) && typeof state.p === 'string' &&
            Number.isFinite(state.began) && Number.isFinite(state.started) &&
            members.every(m => ['T','C','zero'].includes(state.prediction[m]))) return state;
    } catch { /* A damaged session entry opens the original exercise. */ }
}
const state = takePendingReveal();
if (state) {
    field('section-cut').value = String(state.q.cut);
    field('section-centre').value = state.q.centre;
    field('section-side').value = state.q.side;
    field('section-load').value = state.p;
    refresh();
    started = state.started;
    for (const m of members)
        field('predict-' + m).value = state.prediction[m];
    predictionChanged();
    if (state.connected) await session.connect();
    const prior = history().at(-1);
    if (session.courseId === state.courseId && prior &&
        JSON.stringify(JSON.parse(prior.answer).prediction) === JSON.stringify(prediction()) &&
        !button('record-section').disabled) {
        recorded = true;
        void reveal(state.began, true);
    }
}
