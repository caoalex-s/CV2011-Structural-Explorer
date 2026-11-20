/** Predictions belong to the drawn portal and the checked whole-member report. */
import { endConnection, position } from './engine.js';
import type { Model } from './engine.js';
import { absolute, add, binary64, compare, equal, one } from './frame-rational.js';
import type { Fraction } from './frame-rational.js';
import { element as $ } from './ui.js';

export const portalExercise = new URLSearchParams(location.search).get('exercise') === 'portal-absolute-moment';
export const exerciseStep = 'portal_absolute_moment';
export const exerciseStorage = 'cv2011-portal-absolute-moment/v1';

function portalBeam(model: Model) {
    if (model.nodes.length !== 4 || model.members.length !== 3 || model.supports.length !== 2 || model.loads.length !== 1) return;
    const load = model.loads[0];
    const beam = model.members.find(m => m.id === load.member);
    if (!beam || load.kind !== 'distributed' || load.fx !== 0 || load.mz !== 0 || !(load.fy * load.qEnd < 0) ||
        !(0 <= load.t && load.t < load.end && load.end <= 1)) return;
    const b = position(model, beam.id, 0), c = position(model, beam.id, 1);
    if (c.x - b.x !== 6 || b.y !== c.y) return;
    if (model.members.some(m => m.EA !== 2000000 || m.EI !== 20000 || (['a','b'] as const).some(end =>
        Object.values(endConnection(model,m,end)).some(rule => rule !== 'rigid')))) return;
    for (const top of [beam.a, beam.b]) {
        const column = model.members.find(m => m !== beam && (m.a === top || m.b === top));
        if (!column) return;
        const bottom = column.a === top ? 1 : 0;
        const foot = position(model,column.id,bottom);
        const head = position(model,column.id,1-bottom);
        if (foot.x !== head.x || head.y - foot.y !== 4 ||
            !model.supports.some(s => s.kind === 'fixed' && s.member === column.id && s.t === bottom)) return;
    }
    return beam;
}

const rational = (value: string): Fraction => {
    const [n,d] = value.split('/').map(BigInt);
    return { n,d };
};
const metres = (v: Fraction) => Number(v.n * 1000000000000n / v.d) / 1e12;

function peaks(rows: HTMLElement, model: Model) {
    const candidates = Array.from(rows.querySelectorAll<HTMLElement>('[data-field="M"][data-candidate]'))
        .filter(row => row.dataset.min === 'true' || row.dataset.max === 'true')
        .map(row => {
            const data = row.dataset;
            const y0 = rational(data.yLow!), y1 = rational(data.yHigh!);
            const magnitudes = [absolute(y0),absolute(y1)].sort(compare);
            const low = y0.n <= 0n && y1.n >= 0n ? { n:0n,d:1n } : magnitudes[0];
            return { low, high:magnitudes[1], x0:metres(rational(data.xLow!)), x1:metres(rational(data.xHigh!)),
                moment:(metres(y0)+metres(y1))/2, flat:data.side === 'flat' };
        });
    const possible = candidates.filter(a => !candidates.some(b => compare(b.low,a.high)>0)).sort((a,b)=>a.x0-b.x0);
    const distinct = possible.filter((p,i) => !i || p.x0 !== possible[i-1].x0 || p.x1 !== possible[i-1].x1);
    const load = model.loads[0];
    const symmetric = equal(add(binary64(load.t),binary64(load.end)),one) && load.fy === -load.qEnd;
    const resolved = distinct.length === 1 || (distinct.length === 2 && symmetric && distinct[0].moment * distinct[1].moment < 0);
    return { distinct, resolved:resolved && distinct.every(p=>!p.flat && p.x1-p.x0<0.001) };
}

export function createMomentExercise(getModel:()=>Model, selectBeam:(id:string)=>void, refresh:()=>void,
    adjust:(boundaries:{t:number;end:number})=>void, record:(event:string, answer:string, assisted:boolean)=>void) {
    const panel = $('portal-exercise');
    panel.innerHTML = `<h2>Where does the largest |M| occur on BC?</h2>
    <p>Draw AB upwards 4 m, BC to the right 6 m, and CD downwards 4 m. For example, start at A (0, −2) m. Fix both bases and keep the joints rigid. Use EA = 2,000,000 kN and EI = 20,000 kN·m² for all three members.</p>
    <p>Apply a vertical distributed load over BC. In Properties set the downward-positive intensities to +6 kN/m at B and −6 kN/m at C. Measure x from B towards C.</p>
    <label>Predict every location of the largest bending-moment magnitude, in metres from B. Separate multiple locations with commas (tolerance 0.02 m).
    <input id="moment-prediction" autocomplete="off"></label>
    <button id="moment-check">Check prediction</button> <button id="moment-reveal" disabled>Reveal worked solution</button>
    <p id="moment-feedback" role="status"></p><p id="moment-explanation"></p><div id="moment-adjustment"></div><p id="moment-progress"></p>
    <p>After checking the full-span load, change the intensities to +8 and −8 kN/m. Predict again. Then move the start to one-sixth of BC, keep the end at C, and recheck the peak locations.</p>`;
    const input = $<HTMLInputElement>('moment-prediction'), reveal = $<HTMLButtonElement>('moment-reveal');
    const feedback = $('moment-feedback'), explanation = $('moment-explanation');
    const key = exerciseStorage+'/prediction';
    let source = '', prediction = '', count = 0, revealed = false, exposed = false;
    let outcome: ReturnType<typeof peaks> | undefined;
    function save() {
        sessionStorage.setItem(key,JSON.stringify({source,prediction,count,exposed}));
    }
    function bind(binding:string) {
        if (binding === source) return;
        source = binding; prediction = ''; count = 0; exposed = false; revealed = false; outcome = undefined;
        try {
            const saved = JSON.parse(sessionStorage.getItem(key) || '{}');
            if (saved.source === binding) { prediction=saved.prediction; count=saved.count; exposed=saved.exposed; }
        } catch { /* A missing prediction starts a fresh drawing. */ }
        $('moment-adjustment').replaceChildren();
        save(); input.value = prediction; reveal.disabled = true; explanation.textContent = '';
        feedback.textContent = prediction ? 'Checking the prediction for this drawing…' : '';
        document.body.classList.add('moment-locked');
    }
    function grade() {
        if (!outcome || !prediction) return;
        reveal.disabled = false;
        if (!outcome.resolved) {
            feedback.textContent = 'The checked bounds leave the ordering of the candidate magnitudes unresolved. This prediction is ungraded.';
            return;
        }
        const answer = prediction.split(',').map(Number).sort((a,b)=>a-b);
        const correct = answer.length === outcome.distinct.length && outcome.distinct.every((p,i)=>
            answer[i] >= p.x1-0.02 && answer[i] <= p.x0+0.02);
        feedback.textContent = correct ? 'Correct for this drawing.' : 'Check the number and locations of the peaks. You can retry or reveal the worked solution.';
    }
    $('moment-check').onclick = () => {
        const beam = portalBeam(getModel());
        if (!beam) { feedback.textContent = 'Check the beam direction, dimensions, fixed bases, rigid connections, stiffnesses and sign-changing vertical load.'; return; }
        const value = input.value.trim();
        if (!value || !value.split(',').every(v=>v.trim() && Number.isFinite(Number(v)) && Number(v)>=0 && Number(v)<=6)) {
            feedback.textContent='Enter one or more distances between 0 and 6 m.'; return;
        }
        selectBeam(beam.id);
        prediction=value; input.value=value; count++; save();
        record(count===1?'first_prediction':'retry',value,exposed);
        if (outcome) grade();
        else { feedback.textContent='Checking the whole-member extrema for this drawing…'; $('frame-generate').click(); }
    };
    reveal.onclick = () => {
        if (!outcome || !prediction) return;
        revealed = true;
        if (!exposed) record('reveal',prediction,true);
        exposed=true; save(); document.body.classList.remove('moment-locked'); refresh();
        const load=getModel().loads[0], a=6*load.t,b=6*load.end;
        const locations=outcome.distinct.map(p=>'x ≈ '+((p.x0+p.x1)/2).toFixed(4)+' m (M ≈ '+p.moment.toFixed(4)+' kN·m)').join(' and ');
        explanation.textContent='Taking downward w as positive, w(x) = '+(-load.fy)+' + ('+(load.fy-load.qEnd)+')(x − '+a+')/('+b+' − '+a+') kN/m over the loaded interval, and zero elsewhere. Integrate dV/dx = −w and dM/dx = V using the starting values in the checked intervals below. Compare |M| at the ends, load boundaries and interior zeros of V. '+
            (outcome.resolved ? (outcome.distinct.length===2?'Reflection about midspan reverses the load and moment signs, so the two extrema have equal magnitude at ':'The largest magnitude occurs at ') : 'The checked bounds leave these possible locations: ')+locations+'.';
    };
    function status(message:string) {
        if (!prediction || !/limit|timed out|inconclusive|failed|unavailable/i.test(message)) return;
        outcome=undefined; reveal.disabled=true; feedback.textContent=message+' This prediction is ungraded.';
        const host=$('moment-adjustment'); host.replaceChildren();
        const load=getModel().loads[0];
        if (!load || !/limit|timed out/i.test(message)) return;
        const proposed={t:Math.round(load.t*8)/8,end:Math.round(load.end*8)/8};
        if (proposed.t>=proposed.end || proposed.t===load.t && proposed.end===load.end) return;
        const note=document.createElement('p'), button=document.createElement('button');
        note.textContent='The checker reached its resource limit. You can try a different load extent. Start fraction '+load.t+' → '+proposed.t+', end fraction '+load.end+' → '+proposed.end+'. Undo restores the original extent.';
        button.textContent='Apply these load boundaries'; button.onclick=()=>adjust(proposed);
        host.append(note,button);
    }
    return {bind,status, get visible(){return revealed;}, checked(model:Model, member:string, rows:HTMLElement) {
        if (prediction && JSON.stringify(model)===JSON.stringify(getModel()) && portalBeam(model)?.id===member) {
            outcome=peaks(rows,model); grade();
            if (outcome.resolved) {
                const load = model.loads[0];
                const stages = JSON.parse(sessionStorage.getItem(exerciseStorage+'/stages') || '{}');
                if (load.fy === -6 && load.qEnd === 6 && load.t === 0 && load.end === 1) stages.reference = true;
                if (stages.reference && load.fy === -8 && load.qEnd === 8 && load.t === 0 && load.end === 1) stages.magnitude = true;
                if (stages.magnitude && load.fy === -8 && load.qEnd === 8 && (load.t !== 0 || load.end !== 1)) stages.extent = true;
                sessionStorage.setItem(exerciseStorage+'/stages', JSON.stringify(stages));
                $('moment-progress').textContent = 'Drawings checked: '+['reference','magnitude','extent'].filter(stage=>stages[stage]).join(', ')+'.';
            }
        }
    }};
}
