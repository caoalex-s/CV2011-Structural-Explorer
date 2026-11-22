import {createLearningSession} from './learning-session.js';
import {checkDrawing, invalidateCheck, isolateForCheck} from './truss-check.js';
import {rectangle, rectangleCase, joint, solve, validate, exact, number} from './ideal-truss.js';
import type {Drawing, Joint} from './ideal-truss.js';
import {element as el, escapeHtml as esc, downloadJson} from './ui.js';

const storage='cv2011-ideal-truss-v1';
type Event={courseId:string; time:string; action:string; answer:string; drawing:Drawing};
document.body.classList.add('truss-workspace');
let drawingRevision=0;
let pendingRecord:Promise<unknown>=Promise.resolve();
let drawing=rectangle(), events:Event[]=[], chosen='A', tool='edit', start='', predicted=false, revealed=false;
try {
    const saved=JSON.parse(localStorage.getItem(storage)||'null');
    if(saved){ validate(saved.drawing); drawing=saved.drawing; events=saved.events; }
} catch { /* An invalid saved drawing opens the example. */ }
document.querySelector('.topbar nav')!.innerHTML='<a href="./">Frame workspace</a> <a href="learn/">Learn</a>';
document.querySelector('.header-actions')!.innerHTML='<button id="replay">Local replay</button> <button id="settings-button">Session</button> <button id="instructor">Learning insights</button>';
el('workspace').innerHTML=`<h1>Ideal planar truss</h1>
<p>What holds a rectangular panel in shape? Compare the braced panel with the same panel after removing AC or rotating the roller at B.</p>
<div class="modelbar"><button id="rectangle">Reset rectangle</button><button id="blank">Blank drawing</button><button id="diagonal">Remove AC</button><button id="rotate">Rotate roller B</button></div>
<div class="work-grid"><aside class="panel"><h2>Drawing tools</h2><p>Choose a tool, then click the drawing. New joints snap to whole metres.</p>
<select id="truss-tool" aria-label="Drawing tool"><option value="edit">Edit joint</option><option value="joint">Add joint</option><option value="bar">Connect two joints</option><option value="remove">Remove bar</option></select><p id="hint" role="status"></p><div id="inspector"></div></aside>
<section class="canvas-column panel"><svg id="truss-canvas" viewBox="0 0 600 360" aria-label="Ideal truss drawing" style="width:100%;touch-action:manipulation"></svg><p>Coordinates in m. Forces in kN. Positive x points right and positive y points up.</p></section>
<section class="panel"><h2>Predict the response</h2><form id="prediction"><label>Member idealisation <select name="ideal" required><option value="">Choose</option><option>Two-force member</option><option>Member carrying bending moment</option></select></label>
<label>Count m + r − 2j <input name="count" type="number" required></label>
<label>Stability <select name="state" required><option value="">Choose</option><option>Stable and determinate</option><option>Stable and indeterminate</option><option>Mechanism</option></select></label>
<label>Permitted joint motion <input name="motion" required></label><button>Record prediction</button></form><p id="feedback" role="status"></p><button id="reveal" disabled>Reveal equilibrium</button></section></div>
<section id="response" class="panel" hidden></section><section id="history" class="panel" hidden></section><section id="insights-panel" class="panel" hidden></section>`;
const session=createLearningSession({trussOnly:true,notify:message=>{el('hint').textContent=message;},onConnectionChange:()=>session.updateStatus()});
session.updateStatus();
el('instructor').onclick=async()=>{await pendingRecord;el('insights-panel').hidden=false;await session.renderInsights();el('insights-panel').scrollIntoView();};
const svg=document.querySelector<SVGSVGElement>('#truss-canvas')!;
const persist=()=>localStorage.setItem(storage,JSON.stringify({drawing,events}));
function record(action:string,answer:string){events.push({courseId:session.courseId,time:new Date().toISOString(),action,answer,drawing:structuredClone(drawing)});persist();
    const snapshot=structuredClone(drawing);
    pendingRecord=pendingRecord.then(()=>session.record({model:snapshot,section:0,step:'ideal_planar_truss',side:'',hintUsed:false,solutionRevealed:action==='reveal'||action==='assisted retry'},action==='first prediction'?'first_prediction':action==='assisted retry'?'retry':action,answer,'')).catch(error=>{el('hint').textContent=String(error);});
}
function change(edit:(copy:Drawing)=>void){
    try{
        const copy=structuredClone(drawing);edit(copy);validate(copy);
        drawingRevision++;invalidateCheck();drawing=copy;predicted=false;revealed=false;start='';el<HTMLFormElement>('prediction').reset();
        el('response').hidden=true;el('history').hidden=true;el('feedback').textContent='';el<HTMLButtonElement>('reveal').disabled=true;
        persist();paint();
    } catch(error){el('hint').textContent=String(error);}
}
const mode=el<HTMLSelectElement>('truss-tool');
mode.onchange=()=>{tool=mode.value;start='';paint();};
function coordinates(){
    const xs=drawing.joints.map(j=>j.x),ys=drawing.joints.map(j=>j.y);
    const left=Math.min(0,...xs),right=Math.max(4,...xs),bottom=Math.min(0,...ys),top=Math.max(3,...ys);
    const s=Math.min(440/(right-left),220/(top-bottom));
    return {s,left,top,x:(n:number)=>80+(n-left)*s,y:(n:number)=>65+(top-n)*s};
}
function arrow(x:number,y:number,dx:number,dy:number,label:string,color='#aa410f'){
    const length=Math.hypot(dx,dy);if(!length)return '';
    const ex=x+39*dx/length,ey=y-39*dy/length;
    const a=Math.atan2(ey-y,ex-x);
    return `<g stroke="${color}" fill="${color}"><line x1="${x}" y1="${y}" x2="${ex}" y2="${ey}" stroke-width="2"/><path d="M${ex},${ey} l${-8*Math.cos(a-.45)},${-8*Math.sin(a-.45)} L${ex-8*Math.cos(a+.45)},${ey-8*Math.sin(a+.45)} Z"/></g><text x="${ex+4}" y="${ey+3}" font-size="12">${esc(label)}</text>`;
}
function paint(){
    el('prediction').querySelector('button')!.disabled=false;
    if(!drawing.joints.some(j=>j.id===chosen))chosen=drawing.joints[0]?.id||'';
    const c=coordinates(), find=(id:string)=>drawing.joints.find(j=>j.id===id)!;
    svg.innerHTML=drawing.bars.map(([a,b])=>{
        const p=find(a),q=find(b);
        return `<line data-edge="${a}${b}" x1="${c.x(p.x)}" y1="${c.y(p.y)}" x2="${c.x(q.x)}" y2="${c.y(q.y)}" stroke="#264c5a" stroke-width="6"/>`;
    }).join('')+drawing.joints.map(j=>{
        const x=c.x(j.x),y=c.y(j.y);
        const rotation=j.support==='roller'?Math.atan2(j.rx,j.ry)*180/Math.PI:0;
        const support=j.support==='free'?'':`<g transform="translate(${x} ${y}) rotate(${rotation})" stroke="#24586c" fill="#d3e5e8"><path d="M0,3 l-11,17 h22 z"/>${j.support==='pin'?'<path d="M-15,21h30"/>':'<circle cx="-6" cy="24" r="3"/><circle cx="6" cy="24" r="3"/><path d="M-14,28h28"/>'}</g>`;
        return support+arrow(x,y,j.fx,j.fy, '('+j.fx+', '+j.fy+')')+`<circle data-node="${j.id}" cx="${x}" cy="${y}" r="7" fill="${j.id===chosen?'#a84e17':'white'}" stroke="#17465c" stroke-width="2"/><text x="${x-16}" y="${y-11}" font-size="17">${j.id}</text>`;
    }).join('');
    const ac=drawing.bars.some(([a,b])=>[a,b].sort().join('')==='AC');
    el('diagonal').textContent=ac?'Remove AC':'Add AC';
    el<HTMLButtonElement>('diagonal').disabled=!find('A')||!find('C');
    el<HTMLButtonElement>('rotate').disabled=find('B')?.support!=='roller';
    el('hint').textContent=tool==='bar'?(start?'Select the second joint.':'Select the first joint.'):tool==='remove'?'Click a bar to remove it.':'';
    const j=find(chosen);
    el('inspector').innerHTML=j?`<h3>Joint ${j.id}</h3><form id="joint-edit"><label>Joint <select id="choose">${drawing.joints.map(v=>'<option '+(v.id===chosen?'selected':'')+'>'+v.id+'</option>').join('')}</select></label>`+
        (['x','y','fx','fy','rx','ry'] as const).map((k,i)=>`<label>${['x (m)','y (m)','Load x (kN)','Load y (kN)','Roller reaction direction x','Roller reaction direction y'][i]} <input type="number" name="${k}" required value="${j[k]}"></label>`).join('')+
        `<label>Support <select name="support">${['free','pin','roller'].map(s=>'<option '+(s===j.support?'selected':'')+'>'+s+'</option>').join('')}</select></label><button>Apply joint edits</button></form><button id="delete-joint">Delete joint</button>`:'';
    if(!j)return;
    el<HTMLSelectElement>('choose').onchange=e=>{chosen=(e.target as HTMLSelectElement).value;paint();};
    el<HTMLFormElement>('joint-edit').oninput=e=>{
        if((e.target as HTMLElement).id==='choose')return;
        drawingRevision++;invalidateCheck();predicted=false;revealed=false;el('response').hidden=true;
        el<HTMLButtonElement>('reveal').disabled=true;el('prediction').querySelector('button')!.disabled=true;
        el('feedback').textContent='Apply the joint edits before predicting.';
    };
    el<HTMLFormElement>('joint-edit').onsubmit=e=>{
        e.preventDefault();const data=new FormData(e.currentTarget as HTMLFormElement);
        change(copy=>{const v=copy.joints.find(p=>p.id===chosen)!;
            for(const key of ['x','y','fx','fy','rx','ry'] as const)v[key]=Number(data.get(key));
            v.support=data.get('support') as Joint['support'];
        });
    };
    el('delete-joint').onclick=()=>change(copy=>{copy.joints=copy.joints.filter(v=>v.id!==chosen);copy.bars=copy.bars.filter(b=>!b.includes(chosen));});
}
svg.onclick=e=>{
    const node=(e.target as SVGElement).getAttribute('data-node'),edge=(e.target as SVGElement).getAttribute('data-edge');
    if(tool==='joint'){
        if(node)return;
        const point=new DOMPoint(e.clientX,e.clientY).matrixTransform(svg.getScreenCTM()!.inverse()),c=coordinates();
        change(copy=>{const id=[...'ABCDEFGHIJKLMNOPQRSTUVWXYZ'].find(a=>!copy.joints.some(j=>j.id===a));
            if(!id)throw Error('All joint letters are in use.');
            copy.joints.push(joint(id,Math.round((point.x-80)/c.s+c.left),Math.round(c.top-(point.y-65)/c.s)));chosen=id;});
    } else if(tool==='bar'&&node){if(!start){start=node;paint();}else change(copy=>copy.bars.push([start,node]));}
    else if(tool==='remove'&&edge)change(copy=>{copy.bars=copy.bars.filter(pair=>pair.join('')!==edge);});
    else if(node){chosen=node;paint();}
};
el('blank').onclick=()=>change(copy=>{copy.joints=[];copy.bars=[];});
el('rectangle').onclick=()=>change(copy=>Object.assign(copy,rectangle()));
el('diagonal').onclick=()=>change(copy=>{
    const i=copy.bars.findIndex(pair=>[...pair].sort().join('')==='AC');
    if(i<0)copy.bars.push(['A','C']);else copy.bars.splice(i,1);
});
el('rotate').onclick=()=>change(copy=>{const b=copy.joints.find(j=>j.id==='B')!;[b.rx,b.ry]=b.rx===0?[1,0]:[0,1];});
el<HTMLFormElement>('prediction').onsubmit=e=>{
    e.preventDefault();if(!drawing.joints.length){el('feedback').textContent='Add a joint before predicting.';return;}
    const data=Object.fromEntries(new FormData(e.currentTarget as HTMLFormElement));
    const result=solve(drawing),count=result.columns.length-2*drawing.joints.length;
    const state=result.motions.length?'Mechanism':result.redundancy?'Stable and indeterminate':'Stable and determinate';
    const prior=events.filter(event=>event.courseId===session.courseId&&JSON.stringify(event.drawing)===JSON.stringify(drawing));
    record(prior.some(event=>event.action==='reveal')?'assisted retry':prior.length?'retry':'first prediction',JSON.stringify(data));
    predicted=true;el<HTMLButtonElement>('reveal').disabled=false;
    el('feedback').textContent=[data.ideal==='Two-force member'?'Idealisation correct.':'Reconsider the actions at a pin.',
        Number(data.count)===count?'Count correct.':'Recount bars, reaction components and joint equations.',
        data.state===state?'Stability prediction correct.':'Check the independent restraint directions.',
        'Compare your motion with the joint displacements at reveal.'].join(' ');
};
el('reveal').onclick=()=>{if(!predicted)return;record('reveal','');revealed=true;showResponse();};
el('replay').onclick=()=>{
    const panel=el('history');panel.hidden=false;
    panel.innerHTML='<h2>Local replay</h2><p>Predictions and reveals on this device, in submission order.</p>'+
        events.filter(v=>v.courseId===session.courseId).map(v=>'<details><summary>'+esc(v.action)+' · '+esc(v.time)+'</summary><pre>'+esc(v.answer)+'\\n'+esc(JSON.stringify(v.drawing,null,2))+'</pre></details>').join('')+
        '<button id="save-truss-events">Save local replay</button>';
    el('save-truss-events').onclick=()=>downloadJson('ideal-truss-replay.json',events.filter(v=>v.courseId===session.courseId));
    panel.scrollIntoView();
};
paint();

function showResponse(){
    const result=solve(drawing), {columns,rank,motions,compatible,forces,redundancy}=result;
    const family=rectangleCase(drawing),m=drawing.bars.length,r=columns.length-m,j=drawing.joints.length;
    const motionRows=motions.map((mode,i)=>`<p data-motion="${mode.u.map(exact).join(',')}" data-work="${exact(mode.work)}">Mode ${i+1} · ${drawing.joints.map((p,k)=>p.id+' ('+exact(mode.u[2*k])+', '+exact(mode.u[2*k+1])+')').join(', ')}. Virtual work of the joint loads for this motion = ${exact(mode.work)}.</p>`).join('');
    const response=el('response');response.hidden=false;
    response.innerHTML=`<h2>Equilibrium of your drawing</h2><p>Straight bars with frictionless pins and loads applied only at joints carry axial force. Each joint supplies two force equations.</p>
    <p>${m} bars + ${r} reaction components − 2 × ${j} joints = ${m+r-2*j}. The equilibrium matrix has rank ${rank}. There are ${2*j-rank} independent permitted motions and ${redundancy} independent self-equilibrated force systems.</p>`+
    (family==='unbraced'?'<p>The top edge can sway horizontally while A and B stay fixed. This internal mechanism changes the panel shape.</p>':
    family==='horizontal'?'<p>The roller permits vertical motion at B. Its horizontal reaction passes through A, so neither support restrains rigid rotation about A.</p>':'')+
    motionRows+(compatible?'':'<p>The joint loads do nonzero virtual work on a permitted motion. Static equilibrium is impossible for this load.</p>')+
    (compatible&&redundancy?'<p>Joint equilibrium leaves redundant forces undetermined.</p>':'')+
    (family==='braced'?`<h3>Whole-truss equilibrium</h3><p>Let P be the signed horizontal load at C. Here P = ${drawing.joints.find(v=>v.id==='C')!.fx} kN. Taking moments about A gives 4Bᵧ − 3P = 0. Horizontal and vertical equilibrium give Aₓ = −P and Aᵧ = −Bᵧ = −3P/4.</p>
    <h3>Method of joints</h3><p>At unloaded D, the two noncollinear bars each carry zero force. Assume tension acts away from each joint. At C, horizontal equilibrium gives P − (4/5)F_AC = 0. Vertical equilibrium gives −F_BC − (3/5)F_AC = 0. Thus F_AC = 5P/4 and F_BC = −3P/4. At B, horizontal equilibrium gives F_AB = 0.</p>`:'')+
    (forces?`<table aria-label="Forces"><caption>Member forces and support reactions</caption><thead><tr><th>Quantity</th><th>Force (kN)</th><th>Sense</th></tr></thead><tbody>${forces.map((f,i)=>`<tr><th>${f.name}</th><td>${Number(f.value.toPrecision(7))}</td><td>${i<m?(f.coefficient.n>0n?'Tension':f.coefficient.n<0n?'Compression':'Zero'):'Along reaction direction (signed)'}</td></tr>`).join('')}</tbody></table>
    <h3>Joint free bodies</h3><p>Arrows show the force acting on the isolated joint. A zero-force member has no arrow.</p><div id="free-bodies" style="display:flex;flex-wrap:wrap"></div>`:'')+
    (family?'<p id="proof-scope">Reference geometry, connectivity, supports and load pattern match the '+family+' rectangle theorem. The signed load P is a parameter of the proof.</p>':'<p>The rank and equilibrium results for this edited drawing use exact rational elimination.</p>');
    if(forces){
        el('free-bodies').innerHTML=drawing.joints.map((v,i)=>{
            const arrows=forces.map(f=>arrow(85,62,number(f.coefficient)*f.entries[2*i],number(f.coefficient)*f.entries[2*i+1],f.name,'#235870')).join('');
            return `<figure style="margin:8px"><svg width="175" height="125" viewBox="0 0 175 125" aria-label="Joint ${v.id} free body">${arrows}${arrow(85,62,v.fx,v.fy,'P')}<circle cx="85" cy="62" r="4"/></svg><figcaption>Joint ${v.id}</figcaption></figure>`;
        }).join('');
    }
    const equations=document.createElement('details');
    equations.innerHTML='<summary>Joint equilibrium equations</summary><p>Assume tension in each bar. Each coefficient is the component of a unit vector pointing away from the joint. Reaction directions follow the supports.</p><table><thead><tr><th>Joint</th><th>ΣFₓ = 0</th><th>ΣFᵧ = 0</th></tr></thead><tbody>'+jointEquations(drawing,result)+'</tbody></table>';
    response.append(equations);
    const verification=document.createElement('p');verification.setAttribute('role','status');
    const checkButton=document.createElement('button');checkButton.textContent='Check this drawing with Lean';
    response.append(checkButton,verification);
    const run=()=>void checkDrawing(structuredClone(drawing),message=>{verification.textContent=message;});
    checkButton.onclick=async()=>{
        if(crossOriginIsolated){run();return;}
        try{
            const revision=drawingRevision;
            await pendingRecord;
            await isolateForCheck();
            if(revision!==drawingRevision || !revealed)return;
            if(session.connected)sessionStorage.setItem('cv2011-truss-reconnect','1');
            sessionStorage.setItem('cv2011-truss-resume-check',JSON.stringify(drawing));
            location.reload();
        }catch(error){verification.textContent=String(error);}
    };
    if(crossOriginIsolated){verification.textContent='Checking the original drawing locally…';run();}
    response.scrollIntoView();
}


if(sessionStorage.getItem('cv2011-truss-resume-check')===JSON.stringify(drawing)){
    sessionStorage.removeItem('cv2011-truss-resume-check');
    if(sessionStorage.getItem('cv2011-truss-reconnect')==='1'){
        sessionStorage.removeItem('cv2011-truss-reconnect');await session.connect();
    }
    if(events.some(event=>event.courseId===session.courseId&&event.action==='reveal'&&JSON.stringify(event.drawing)===JSON.stringify(drawing))){
        predicted=revealed=true;el<HTMLButtonElement>('reveal').disabled=false;showResponse();
    }
}

function jointEquations(d:Drawing, result:ReturnType<typeof solve>){
    const geometry=(value:number, length:number)=>{
        if(Number.isInteger(length))return length===1?String(value):String(value)+'/'+length;
        return String(value)+'/√'+Math.round(length*length);
    };
    return d.joints.map((j,i)=>{
        const equation=(axis:number)=>{
            const load=axis===0?j.fx:j.fy;
            const terms=load?[String(load)]:[];
            result.columns.forEach((c,k)=>{
                const component=c.entries[2*i+axis];
                if(component)terms.push('('+geometry(component,c.length)+') '+(k<d.bars.length?'F_':'R_')+c.name);
            });
            return (terms.join(' + ')||'0')+' = 0';
        };
        return '<tr><th>'+j.id+'</th><td>'+equation(0)+'</td><td>'+equation(1)+'</td></tr>';
    }).join('');
}
