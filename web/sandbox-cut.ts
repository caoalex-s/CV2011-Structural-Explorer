/** A separate inspection target for the selected member. Stations and cut faces
 * are owned by the workspace; the grip never writes to the drawing or history. */
export interface CutTrack {
    member: string;
    start: {x: number; y: number};
    end: {x: number; y: number};
    parameter: number;
    face: 'left' | 'right';
    stations: number[];
}

export function createSandboxCut(svg: SVGSVGElement, change: (t: number, face: 'left'|'right', preview: boolean) => void) {
    const ns = 'http://www.w3.org/2000/svg';
    const grip = document.createElementNS(ns,'g');
    grip.id = 'sandbox-cut-grip';
    grip.setAttribute('role','slider');
    grip.setAttribute('tabindex','0');
    grip.setAttribute('aria-label','Cut position on selected member');
    grip.setAttribute('aria-valuemin','0');
    grip.setAttribute('aria-valuemax','1');
    grip.innerHTML = '<title>Drag cut along member. Left and right arrows move the cut. Up and down choose the right or left face.</title><rect class="cut-hit" x="-28" y="-22" width="56" height="44" fill="transparent"/><rect class="cut-tab" x="-26" y="-13" width="52" height="26" rx="6"/><path class="grip-axis" d="M-6 0H6m-3-3 3 3-3 3M-3-3l-3 3 3 3"/><text x="6" text-anchor="middle" y="4">Cut</text>';
    const axis = grip.querySelector('.grip-axis')!;
    const leader = document.createElementNS(ns,'path');
    leader.setAttribute('class','cut-grip-leader');
    svg.append(leader,grip);
    let track: CutTrack | undefined;
    let drag: {pointer:number; member:string; t:number; face:'left'|'right'; startX:number; startY:number; offsetX:number; offsetY:number} | undefined;
    let offsetX = 0, offsetY = 0;

    function update(next?: CutTrack) {
        track = next;
        grip.style.display = leader.style.display = next ? '' : 'none';
        if (!next) return;
        const matrix = svg.getScreenCTM();
        if (!matrix) return;
        const scale = matrix.a, bounds = svg.viewBox.baseVal;
        const dx = next.end.x-next.start.x, dy = next.end.y-next.start.y;
        const length = Math.hypot(dx,dy);
        if (length === 0) return;
        axis.setAttribute('transform',`translate(-13 0) rotate(${Math.atan2(dy,dx)*180/Math.PI})`);
        const x = next.start.x+dx*next.parameter, y = next.start.y+dy*next.parameter;
        // Prefer the space below a beam or beside a column. Keep the touch
        // target away from action labels, joints and the point-force handle.
        let gx = x, gy = y;
        if (drag && drag.member === next.member) {
            gx += drag.offsetX; gy += drag.offsetY;
        } else {
            const obstacles = Array.from(svg.querySelectorAll<SVGGraphicsElement>(
                '[data-object] text,[data-vector] text,[data-vector] .hit,[data-object="support"],.node-label,.cut-ordinate,.cut-face-label,.drawing-scale'
            ), element=>element.getBoundingClientRect());
            // The transparent first circle is the full force-rotation target.
            // Give it priority over captions even in a crowded support region.
            const rotation = svg.querySelector('[data-rotate-force] circle')?.getBoundingClientRect();
            const preferred = dx < 0 ? -1 : 1;
            let best = Infinity;
            const lanes = [[47,0],[-47,0],[70,0],[-70,0],[48,60],[48,-60],[-48,60],[-48,-60]];
            for (const [distance, along] of lanes) {
                const px = Math.max(29/scale, Math.min(bounds.width-29/scale,x+(-dy*preferred*distance+dx*along)/(length*scale)));
                const py = Math.max(23/scale, Math.min(bounds.height-23/scale,y+(dx*preferred*distance+dy*along)/(length*scale)));
                const centre = new DOMPoint(px,py).matrixTransform(matrix);
                let cost = Math.hypot(distance,along) + (distance<0 ? 5 : 0);
                if (rotation && centre.x+31 > rotation.left && centre.x-31 < rotation.right &&
                    centre.y+25 > rotation.top && centre.y-25 < rotation.bottom) continue;
                for (const rect of obstacles) {
                    const w = Math.min(centre.x+29,rect.right)-Math.max(centre.x-29,rect.left);
                    const h = Math.min(centre.y+23,rect.bottom)-Math.max(centre.y-23,rect.top);
                    if (w>0 && h>0) cost += w*h;
                }
                if (cost < best) {best=cost; gx=px; gy=py;}
            }
        }
        offsetX = gx-x; offsetY = gy-y;
        leader.setAttribute('d',`M${x} ${y}L${gx} ${gy}`);
        grip.setAttribute('transform',`translate(${gx} ${gy}) scale(${1/scale})`);
        grip.setAttribute('aria-valuenow',String(next.parameter));
        grip.setAttribute('aria-valuetext',`${next.member}, t = ${next.parameter}, just ${next.face}`);
    }
    grip.onpointerdown = event => {
        if (!track || event.button !== 0 || drag) return;
        if (event.pointerType === 'touch' && !grip.contains(document.elementFromPoint(event.clientX,event.clientY))) return;
        event.stopPropagation();
        grip.focus({preventScroll:true});
        drag = {pointer:event.pointerId,member:track.member,t:track.parameter,face:track.face,
            startX:event.clientX,startY:event.clientY,offsetX,offsetY};
        grip.setPointerCapture(event.pointerId);
    };
    function move(event: PointerEvent) {
        if (!drag || !track || drag.pointer !== event.pointerId || drag.member !== track.member) return;
        event.stopPropagation();
        const scale = svg.getScreenCTM()?.a;
        if (!scale) return;
        const dx=(track.end.x-track.start.x)*scale, dy=(track.end.y-track.start.y)*scale;
        const length = Math.hypot(dx,dy);
        if (!length) return;
        const delta = ((event.clientX-drag.startX)*dx + (event.clientY-drag.startY)*dy)/(length*length);
        if (!delta && track.parameter === drag.t) return;
        let t = Math.max(0, Math.min(1,drag.t+delta));
        const nearest = track.stations.reduce((best,s) => Math.abs(s-t)<Math.abs(best-t) ? s : best);
        if (Math.abs(t-nearest)*length <= 6) t=nearest;
        change(t,drag.face,true);
    }
    grip.onpointermove = move;
    function finish(event: PointerEvent, cancel: boolean) {
        if (!drag || drag.pointer !== event.pointerId) return;
        event.stopPropagation();
        if (!cancel) move(event);
        const previous = drag;
        drag = undefined;
        if (grip.hasPointerCapture(event.pointerId)) grip.releasePointerCapture(event.pointerId);
        if (track?.member === previous.member)
            change(cancel ? previous.t : track.parameter, cancel ? previous.face : track.face,false);
        update(track);
    }
    grip.onpointerup = event => finish(event,false);
    grip.onpointercancel = grip.onlostpointercapture = event => finish(event,true);
    grip.onkeydown = event => {
        if (!track) return;
        const {parameter,face,stations} = track;
        let t = parameter, side = face;
        switch (event.key) {
            case 'Home': t=0; break;
            case 'End': t=1; break;
            case 'ArrowLeft': t=Math.max(0,parameter-.001); t=Math.max(t,...stations.filter(s=>s<parameter && s>t)); break;
            case 'ArrowRight': t=Math.min(1,parameter+.001); t=Math.min(t,...stations.filter(s=>s>parameter && s<t)); break;
            case 'ArrowDown': side='left'; break;
            case 'ArrowUp': side='right'; break;
            default: return;
        }
        event.preventDefault();
        change(t,side,false);
    };
    return update;
}
