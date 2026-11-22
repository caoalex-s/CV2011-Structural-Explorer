import { PortalRuntime } from './portal-runtime.js';
import { integer, fraction, mul, equal, neg } from './frame-rational.js';
import { solve } from './ideal-truss.js';
import type { Drawing } from './ideal-truss.js';

export function packet(drawing:Drawing) {
    const lines=['TRUSS1',String(drawing.joints.length)];
    for(const j of drawing.joints)lines.push([j.id,j.x,j.y,j.support,j.rx,j.ry,j.fx,j.fy].join(','));
    for(const bar of drawing.bars)lines.push(bar.join(','));
    return new TextEncoder().encode(lines.join('\n'));
}

/** Compare the independently eliminated integer rows with the displayed values.
    A null vector and its work may use any common nonzero normalization. */
export function agrees(drawing:Drawing, bytes:Uint8Array) {
    const result=solve(drawing), lines=new TextDecoder().decode(bytes).split('\n');
    if(lines.shift()!=='TRUSS1'||lines.shift()!==String(result.rank))return false;
    for(const motion of result.motions) {
        const row=lines.shift()?.split(',');
        if(row?.shift()!=='M'||row.length!==motion.u.length+1)return false;
        const values=row.map(v=>fraction(BigInt(v))), expected=[neg(motion.work),...motion.u];
        const pivot=expected.findIndex(v=>v.n!==0n);
        if(pivot<0||values[pivot].n===0n||!expected.every((v,k)=>equal(mul(v,values[pivot]),mul(values[k],expected[pivot]))))return false;
    }
    for(const force of result.forces??[]){
        const fields=lines.shift()?.split(',');
        if(fields?.length!==3||fields[0]!=='F'||!equal(force.coefficient,fraction(BigInt(fields[1]),BigInt(fields[2]))))return false;
    }
    return lines.length===0;
}

let runtime:PortalRuntime|undefined, revision=0;
export function invalidateCheck(){revision++;runtime?.invalidate();}
export async function checkDrawing(drawing:Drawing,notify:(text:string)=>void) {
    const version=++revision;
    try {
        const prefix=location.pathname.includes('/portal-checker/')?'./':'./portal-checker/';
        if(!runtime||runtime.needsReset)runtime=new PortalRuntime(new URL(prefix+'ideal-truss/worker.mjs',location.href));
        await runtime.ready;
        if(version!==revision)return;
        const answer=await runtime.checkDiagram(packet(drawing),true);
        if(version!==revision)return;
        if(answer.state!=='accepted'||!(answer.report instanceof Uint8Array)||!agrees(drawing,answer.report)) throw Error('The compiled checker did not confirm the displayed results.');
        notify('Lean checked this drawing by exact computation. The displayed rank, permitted motions, load compatibility and force coefficients agree with the compiled Lean calculation from the joint and bar data. Drawing packet SHA-256 '+answer.inputDigest+'.');
    } catch(error){if(version===revision)notify('Local check unavailable. '+String(error));}
}

export async function isolateForCheck() {
    const scope=new URL('./',location.href);
    const script=new URL(scope.pathname.endsWith('/portal-checker/')?'isolation-sw.js':'main-checker-sw.js',scope).href;
    const existing=await navigator.serviceWorker.getRegistration(scope.href);
    if(existing&&existing.scope===scope.href&&[existing.active,existing.waiting,existing.installing].some(w=>w&&w.scriptURL!==script))throw Error('Another service worker owns this scope.');
    await navigator.serviceWorker.register(script,{scope:scope.href});
    await navigator.serviceWorker.ready;
    if(navigator.serviceWorker.controller?.scriptURL!==script)await new Promise<void>((resolve,reject)=>{
        const onChange=()=>{if(navigator.serviceWorker.controller?.scriptURL===script){clearTimeout(timer);navigator.serviceWorker.removeEventListener('controllerchange',onChange);resolve();}};
        const timer=setTimeout(()=>{navigator.serviceWorker.removeEventListener('controllerchange',onChange);reject(Error('Timed out enabling the local checker.'));},10000);
        navigator.serviceWorker.addEventListener('controllerchange',onChange);onChange();
    });
}
