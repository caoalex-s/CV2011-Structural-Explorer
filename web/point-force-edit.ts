/** Both the drawing handle and the inspector edit the same force components. */
import { angleVector, type Load } from './engine.js';

const zeroAngles = new WeakMap<Load, number>();
const strengths = new WeakMap<Load, number>();

export const pointAngle = (load: Load) => load.fx || load.fy
    ? Math.atan2(load.fy,load.fx)*180/Math.PI : zeroAngles.get(load) ?? 0;
export const forceMagnitude = (load: Load) => strengths.get(load) ?? Math.hypot(load.fx,load.fy);

export function setPointForce(load: Load, angle: number, magnitude = forceMagnitude(load)) {
    const axis = angleVector(angle);
    strengths.set(load,magnitude);
    load.fx = magnitude * axis.x;
    load.fy = magnitude * axis.y;
    if (!magnitude) zeroAngles.set(load,angle);
}
export function componentsEdited(load: Load) { strengths.delete(load); }
