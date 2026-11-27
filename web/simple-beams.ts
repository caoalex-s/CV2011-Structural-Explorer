import { math, measureUnits, quantity } from './math.js';
import { beamDrawing, cutDrawing, cutEquations } from './lesson-view.js';
import { beamValues, initialBeam, lessonBeam, retainsPointLoad, type CutSide } from './lesson-beam.js';
import { checkBeam, invalidateBeamCheck } from './beam-cut-check.js';
import { isolateForCheck } from './truss-check.js';
import { createLearningSession } from './learning-session.js';
import { showTrussNavigation } from './truss-navigation.js';
import { element as el, escapeHtml } from './ui.js';

showTrussNavigation('simple-beams');
document.body.classList.add('truss-workspace', 'section-workspace', 'simple-beams');
const options = '<option value="">Choose</option><option value="drop">Drops</option><option value="rise">Rises</option><option value="same">Stays continuous</option>';
el('workspace').innerHTML = `<header class="exercise-heading"><p class="course-reference">Weeks 4–5 · Internal actions</p><h1>Simple beams</h1></header>
<p class="exercise-intro">What happens to the shear force V and bending moment M as a cut crosses a downward point load?</p>
<div class="section-task"><section class="section-model"><div class="beam-cut-sheet"><svg id="beam-model" role="img" viewBox="0 0 760 245"></svg>
<button id="beam-cut-grip" type="button" role="slider" aria-label="Drag cut along beam" aria-valuemin="1" aria-valuemax="32"><span aria-hidden="true">↔</span> Drag cut</button></div>
<p id="beam-cut-feedback" hidden></p>
<div class="section-controls"><label>Downward load P (kN)<input id="beam-load" type="number" min="5" max="50" step="1" value="20"></label>
<label>Cut position <output id="beam-station" for="beam-cut"></output><input type="range" id="beam-cut" min="1" max="32" value="16"></label></div>
<button id="beam-left-limit">Just left of P</button> <button id="beam-right-limit">Just right of P</button></section>
<section class="section-prediction"><h2>Predict the change from left to right</h2><div class="section-controls">
<label>Shear force V<select id="beam-predict-v">${options}</select></label><label>Bending moment M<select id="beam-predict-m">${options}</select></label></div>
<button id="beam-record" disabled>Record prediction</button> <button id="beam-reveal" disabled>Check this cut</button>
<p id="beam-status" role="status"></p><p id="beam-storage"></p></section></div>
<section id="beam-answer" class="panel" hidden></section><section id="history" class="panel" hidden></section><section id="insights-panel" class="panel" hidden></section>`;
const load = el<HTMLInputElement>('beam-load'), cut = el<HTMLInputElement>('beam-cut');
const shear = el<HTMLSelectElement>('beam-predict-v'), moment = el<HTMLSelectElement>('beam-predict-m');
const record = el<HTMLButtonElement>('beam-record'), reveal = el<HTMLButtonElement>('beam-reveal');
const inputs = () => ({ ...initialBeam, load: load.valueAsNumber });
const prediction = () => ({ shear: shear.value, moment: moment.value });
const valid = () => load.value !== '' && load.validity.valid;
const session = createLearningSession({ exercise: 'simple_beams', notify: msg => { el('beam-status').textContent = msg; }, onConnectionChange: storage });
function storage() {
    session.updateStatus();
    el('beam-storage').textContent = session.connected ? 'Attempts are saved in this browser and sent to the connected local instructor.' : 'Your attempts are saved in this browser. Open Local replay to review them.';
}
storage();
let revision = 0, recorded = false, opened = false, pending: Promise<unknown> = Promise.resolve();
const resumeKey = 'cv2011-simple-beams-resume';
function station() {
    const index = Number(cut.value), x = (index <= 16 ? index : index - 1) / 4;
    const side: CutSide = index <= 16 ? 'left' : 'right';
    return { x, side, parameter: x / 8, description: x + ' m' + (x === 4 ? ' (' + side + ' limit)' : '') };
}
function clear() {
    revision++;
    invalidateBeamCheck();
    el('beam-cut-feedback').hidden = true;
    el('beam-answer').replaceChildren();
    el('beam-answer').hidden = true;
    el('beam-status').textContent = '';
}
function showCutValues(scope: string, shear: number, moment: number) {
    const feedback = el('beam-cut-feedback');
    const q = station();
    const face = q.x === 4 ? ' (just ' + q.side + ')' : '';
    const value = (variable: string, amount: number, unit: string) =>
        math(variable + '=' + quantity(amount > 0 ? '+' + amount : String(amount),unit));
    feedback.innerHTML = `<b>${scope}</b><span>${math('x=' + quantity(String(q.x),measureUnits.length))}${face}</span>
        <span>${value('V',shear,measureUnits.force)}</span><span>${value('M',moment,measureUnits.moment)}</span>`;
    feedback.hidden = false;
}
const grip = el<HTMLButtonElement>('beam-cut-grip');
function refreshModel() {
    const { parameter, description } = station();
    el('beam-station').textContent = description;
    cut.setAttribute('aria-valuetext', description);
    grip.style.left = ((100 + 560 * parameter) / 760 * 100) + '%';
    grip.hidden = !valid();
    grip.setAttribute('aria-valuenow', cut.value);
    grip.setAttribute('aria-valuetext', description);
    grip.classList.toggle('at-load', parameter === inputs().position);
    for (const [button, index] of [['beam-left-limit','16'],['beam-right-limit','17']])
        el(button).setAttribute('aria-pressed', String(index === cut.value));
    const cutX = 100 + 560 * parameter;
    el('beam-model').innerHTML = valid() ? beamDrawing(inputs(), parameter, false, 'pin-roller', false) +
        `<path class="section-line" d="M${cutX} 90V172 M${cutX} 234v11"><title>Cut at ${description}</title></path>` : '';
}
function resetPrediction() {
    clear(); opened = false; recorded = false;
    record.disabled = !valid() || !shear.value || !moment.value;
    reveal.disabled = true;
}
load.oninput = () => {
    shear.value = moment.value = ''; resetPrediction(); refreshModel();
    if (!valid()) el('beam-status').textContent = 'Enter a whole-number load from 5 to 50 kN.';
};
shear.oninput = moment.oninput = resetPrediction;
function moveCut(preview = false) {
    clear(); refreshModel();
    reveal.disabled = !recorded;
    if (opened && preview) {
        const q = station(), values = beamValues(inputs(),q.parameter,q.side);
        showCutValues('Numerical preview',values.shear,values.moment);
        el('beam-answer').innerHTML = `<h2>Retained left free body at ${q.description}</h2>
            <svg id="beam-fbd" role="img" viewBox="0 0 760 235">${cutDrawing(inputs(),q.parameter,q.side)}</svg>
            <p>Numerical preview · V = ${signed(values.shear)} kN · M = ${signed(values.moment)} kN·m</p>`;
        el('beam-answer').hidden = false;
        el('beam-status').textContent = 'Release the cut to check equilibrium.';
    } else if (opened) void check(false);
}
cut.oninput = () => moveCut();
function selectStation(index: number, preview = false) {
    const value = String(Math.max(1,Math.min(32,index)));
    if (value === cut.value) return;
    cut.value = value;
    moveCut(preview);
}
// Both faces of the point load share a drawing coordinate. Within its snap
// interval the approach side selects the limit. The buttons permit either face.
let drag: {pointer: number; start: number; offset: number; moved: boolean} | undefined;
const sheet = grip.parentElement!;
const coordinate = (clientX: number) => {
    const box = sheet.getBoundingClientRect();
    return ((clientX-box.left) / box.width * 760 - 100) / 560 * 32;
};
grip.onpointerdown = event => {
    if (drag || event.button !== 0) return;
    drag = {pointer:event.pointerId, start:Number(cut.value),
        offset:coordinate(event.clientX) - station().parameter * 32, moved:false};
    grip.setPointerCapture(event.pointerId);
};
function track(event: PointerEvent) {
    if (!drag || drag.pointer !== event.pointerId) return;
    const raw = coordinate(event.clientX) - drag.offset;
    const tick = Math.round(raw);
    const index = tick === 16 ? (Math.abs(raw-16) < 0.015 ? (Number(cut.value) <= 16 ? 16 : 17) : raw < 16 ? 16 : 17)
        : tick + (tick > 16 ? 1 : 0);
    const old = cut.value;
    selectStation(index,true);
    if (old !== cut.value) drag.moved = true;
}
grip.onpointermove = track;
function finish(event: PointerEvent, cancel: boolean) {
    if (!drag || drag.pointer !== event.pointerId) return;
    if (!cancel) track(event);
    const gesture = drag;
    drag = undefined;
    if (grip.hasPointerCapture(event.pointerId)) grip.releasePointerCapture(event.pointerId);
    if (!gesture.moved) return;
    if (cancel) cut.value = String(gesture.start);
    moveCut();
}
grip.onpointerup = event => finish(event,false);
grip.onpointercancel = grip.onlostpointercapture = event => finish(event,true);
grip.onkeydown = event => {
    const change: Record<string,number> = {ArrowLeft:-1,ArrowDown:-1,ArrowRight:1,ArrowUp:1,Home:-32,End:32};
    if (!(event.key in change)) return;
    event.preventDefault();
    selectStation(Number(cut.value) + change[event.key]);
};
for (const [id, value] of [['beam-left-limit','16'],['beam-right-limit','17']])
    el(id).onclick = () => { cut.value = value; moveCut(); };
const history = () => session.beamEvents().filter(a => JSON.stringify(a.model) === JSON.stringify(lessonBeam(inputs())));
function log(event: string, assisted: boolean) {
    const q = station();
    pending = session.record({ model: lessonBeam(inputs()), section: q.parameter, side: q.side, step: 'simple_beams', hintUsed: false, solutionRevealed: assisted },
        event, JSON.stringify({ prediction: prediction(), x: q.x, side: q.side }), 'kN, kN·m', pending);
}
record.onclick = () => {
    resetPrediction();
    const prior = history();
    log(prior.length ? 'retry' : 'first_prediction', prior.some(a => a.event === 'reveal'));
    recorded = true; reveal.disabled = false;
    el('beam-status').textContent = 'Prediction recorded. Check the cut, then move it across P.';
};
const signed = (value: number) => value > 0 ? '+' + value : String(value).replace('-', '−');
async function check(logReveal: boolean, resumed = false) {
    if (!recorded || !valid()) return;
    const current = revision;
    reveal.disabled = true;
    el('beam-status').textContent = 'Checking equilibrium for this cut…';
    try {
        if (!crossOriginIsolated) {
            if (resumed) throw Error('Browser isolation did not start.');
            await Promise.all([isolateForCheck(), pending]);
            if (revision !== current) return;
            sessionStorage.setItem(resumeKey, JSON.stringify({ load: load.value, cut: cut.value, prediction: prediction(), connected: session.connected, courseId: session.courseId }));
            location.reload(); return;
        }
        const q = station(), beam = inputs(), receipt = await checkBeam(beam, q.parameter, q.side);
        if (!receipt || revision !== current) return;
        opened = true;
        const { Ay, By, shear: V, moment: M } = receipt.values;
        showCutValues('Checked cut',V,M);
        const includes = retainsPointLoad(q.parameter, beam.position, q.side);
        const count = Number(shear.value === 'drop') + Number(moment.value === 'same');
        el('beam-answer').innerHTML = `<h2>Equilibrium at ${q.description}</h2><p>Taking moments about A gives B<sub>y</sub> = P × 4 / 8 = ${By} kN. Vertical equilibrium gives A<sub>y</sub> = P − B<sub>y</sub> = ${Ay} kN.</p>
        <h3>Retained left free body</h3><svg id="beam-fbd" role="img" viewBox="0 0 760 235">${cutDrawing(beam,q.parameter,q.side)}</svg>
        <p>The arrows at the cut show the assumed positive directions.</p>${cutEquations(beam,q.parameter,q.side)}
        <p>V = ${Ay} kN${includes ? ' − ' + beam.load + ' kN' : ''} = <strong>${signed(V)} kN</strong></p>
        <p>M = (${Ay} kN)(${q.x} m)${includes ? ' − (' + beam.load + ' kN)(' + (q.x-4) + ' m)' : ''} = <strong>${signed(M)} kN·m</strong></p>
        <p>${count} of your 2 predictions agree. Across P, shear drops by ${beam.load} kN. Bending moment is continuous because the point load has zero lever arm at the cut and there is no applied couple.</p>
        <details><summary>Local check receipt</summary><pre id="beam-receipt"></pre></details>`;
        el('beam-receipt').textContent = JSON.stringify(receipt,null,2);
        el('beam-answer').hidden = false;
        el('beam-status').textContent = 'Compiled Lean checked the reactions and internal actions for this beam, cut position and side.';
        if (logReveal) log('reveal', true);
    } catch (error) {
        if (revision === current) { reveal.disabled = false; el('beam-status').textContent = String(error); }
    }
}
reveal.onclick = () => void check(!opened);
el('replay').onclick = async () => {
    await pending;
    el('history').innerHTML = '<h2>Local replay</h2>' + session.beamEvents().map(a => '<details><summary>' + escapeHtml(a.event.replaceAll('_',' ') + ' · ' + a.timestamp) + '</summary><pre>' + escapeHtml(a.answer) + '</pre></details>').join('');
    el('history').hidden = false; el('history').scrollIntoView();
};
el('instructor').onclick = async () => { await pending; el('insights-panel').hidden = false; await session.renderInsights(); el('insights-panel').scrollIntoView(); };
refreshModel();
const saved = sessionStorage.getItem(resumeKey);
sessionStorage.removeItem(resumeKey);
if (saved) {
    try {
        const state = JSON.parse(saved);
        load.value = state.load; cut.value = state.cut;
        shear.value = state.prediction.shear; moment.value = state.prediction.moment;
        resetPrediction(); refreshModel();
        if (state.connected) await session.connect();
        const last = valid() && history().at(-1);
        if (last && session.courseId === state.courseId && !record.disabled && JSON.stringify(JSON.parse(last.answer).prediction) === JSON.stringify(prediction())) {
            recorded = true; void check(true, true);
        }
    } catch { el('beam-status').textContent = 'Record a prediction to check the current cut.'; }
}
