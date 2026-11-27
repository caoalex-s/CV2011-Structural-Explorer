/** Interactive direction in global coordinates. The SVG uses screen y downward. */
export const wrap = (angle: number) => (angle % 360 + 360) % 360;
const angularDistance = (a: number, b: number) => Math.abs(wrap(a - b + 180) - 180);

/** One snap latch per gesture, shared by the dial and the drawing handle. */
export function angleSnap(start: number, grab: boolean) {
    const initial = wrap(Math.round(start/45)*45);
    let held = grab && angularDistance(initial,start)<1e-9 ? initial : undefined;
    return (raw: number) => {
        const nearest = wrap(Math.round(raw/45)*45);
        if (held !== undefined && angularDistance(raw,held)>6) held = undefined;
        if (held === undefined && angularDistance(raw,nearest)<=3) held = nearest;
        return held ?? wrap(Math.round(raw*100)/100);
    };
}

export function directionDial(angle: number, line: boolean): string {
    const ticks = Array.from({length: 8}, (_, i) =>
        `<path transform="rotate(${45*i})" d="M44 0h4"/>`).join('');
    return `<svg class="direction-dial" viewBox="-64 -64 128 128" role="slider" tabindex="0"
        aria-label="${line ? 'Positive intensity direction' : 'Force direction'}" aria-describedby="dial-help"
        aria-valuemin="0" aria-valuemax="360" aria-valuenow="${angle}" aria-valuetext="${angle} degrees counterclockwise from global positive x">
        <circle class="dial-face" r="62"/><circle class="dial-track" r="40"/>
        <g class="dial-ticks">${ticks}</g>
        <g class="dial-axes" aria-hidden="true"><text x="55" y="3">+<tspan>x</tspan></text><text x="0" y="-51">+<tspan>y</tspan></text></g>
        <g class="indicator-pointer" transform="rotate(${-angle})">
          <path d="M-10 -2H18V-6L29 0 18 6V2H-10Z"/><circle class="dial-handle" cx="40" cy="0" r="7"/>
        </g><circle class="dial-pivot" r="3"/></svg>`;
}

export function bindDirectionDial(dial: SVGSVGElement, edit: (degrees: number, first: boolean) => void): void {
    let degrees = Number(dial.getAttribute('aria-valuenow'));
    let pointer: number | undefined;
    let snap = angleSnap(degrees,false);
    let changed = false;
    let startX = 0, startY = 0, grabbingHandle = false, grabOffset = 0;

    function apply(next: number) {
        if (angularDistance(next,degrees) < 1e-9) return;
        degrees = next;
        edit(next,!changed);
        changed = true;
        dial.querySelector('.indicator-pointer')!.setAttribute('transform',`rotate(${-next})`);
        dial.setAttribute('aria-valuenow',String(next));
        dial.setAttribute('aria-valuetext',next + ' degrees counterclockwise from global positive x');
    }
    function pointerAngle(event: PointerEvent): number | undefined {
        const box = dial.getBoundingClientRect();
        const x = event.clientX - (box.left + box.width/2);
        const y = box.top + box.height/2 - event.clientY;
        if (Math.hypot(x,y) < box.width*.09) return; // Direction is undefined at the centre.
        return wrap(Math.atan2(y,x)*180/Math.PI);
    }
    function move(event: PointerEvent) {
        if (pointer !== event.pointerId) return;
        if (grabbingHandle && Math.hypot(event.clientX-startX,event.clientY-startY) < 3) return;
        grabbingHandle = false;
        const angle = pointerAngle(event);
        if (angle === undefined) return;
        const raw = wrap(angle + grabOffset);
        apply(snap(raw));
    }
    dial.onpointerdown = event => {
        if (pointer !== undefined || event.button !== 0) return;
        const angle = pointerAngle(event);
        if (angle === undefined) return;
        event.preventDefault();
        dial.focus({preventScroll:true});
        pointer = event.pointerId;
        dial.setPointerCapture(pointer);
        const handle = dial.querySelector('.dial-handle')!.getBoundingClientRect();
        startX = event.clientX; startY = event.clientY;
        grabbingHandle = Math.hypot(startX-handle.left-handle.width/2,startY-handle.top-handle.height/2) <= handle.width/2+4;
        grabOffset = grabbingHandle ? degrees-angle : 0;
        snap = angleSnap(degrees,grabbingHandle);
        changed = false;
        move(event);
    };
    dial.onpointermove = move;
    function finish(id: number) {
        if (id !== pointer) return;
        pointer = undefined;
        changed = false;
        if (dial.hasPointerCapture(id)) dial.releasePointerCapture(id);
    }
    dial.onpointerup = event => { move(event); finish(event.pointerId); };
    dial.onpointercancel = event => finish(event.pointerId);
    dial.onlostpointercapture = event => finish(event.pointerId);
    dial.onblur = () => { if (pointer !== undefined) finish(pointer); };
    dial.onkeydown = event => {
        if (event.key === 'Escape' && pointer !== undefined) { finish(pointer); return; }
        if (pointer !== undefined || event.ctrlKey || event.altKey || event.metaKey) return;
        const step = event.shiftKey ? 10 : 1;
        const increments: Record<string,number> = {ArrowUp:step,ArrowRight:step,ArrowDown:-step,ArrowLeft:-step,PageUp:45,PageDown:-45};
        let next = degrees + increments[event.key];
        if (event.key === 'Home') next = 0;
        if (event.key === 'End') next = 359;
        if (!Number.isFinite(next)) return;
        event.preventDefault();
        changed = false;
        apply(wrap(next));
        changed = false;
    };
}
