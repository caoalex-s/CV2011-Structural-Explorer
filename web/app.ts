/** Workspace controller: model/history ownership, pointer interaction, and canvas drawing.
 * Presentation is delegated to inspector.ts, responses.ts, workspace-controls.ts,
 * and worked.ts. learning-session.ts owns connection settings and submitted records.
 * New lesson pages can supply models through this boundary without changing engine.ts.
 */
import { setWorkspaceBusy } from './workspace-readiness.js';
import { analyse, example, lineLoadAxis, position, splitMember, nodeLabels, referenceMember } from './engine.js';
import type { Model, Analysis, Point, Member, Support, Load, Sample } from './engine.js';
import { courseColors, forceSymbol, momentSymbol, rotationalSpring, supportShape, symbolLabel } from './symbols.js';
import { renderWorked, showWorkedSolution } from './worked.js';
import { renderCourseConventions } from './course.js';
import { assignLoadLabels, loadLabels } from './load-labels.js';
import { workspaceConventions } from './axes.js';
import { math, measureUnits, quantity } from './math.js';
import { element as $, escapeHtml as escape, formatNumber as number, formatSectionResult, downloadJson as download } from './ui.js';
import { jointConnections, memberLabel } from './model-view.js';
import type { Selection } from './model-view.js';
import { angleSnap, wrap } from './direction-dial.js';
import { pointAngle, setPointForce } from './point-force-edit.js';
import { renderInspector } from './inspector.js';
import { renderResponses, sampleSection } from './responses.js';
import { sectionFreeBody } from './section-free-body.js';
import { createSandboxCut } from './sandbox-cut.js';
import { createDrawingWorkspace } from './drawing-workspace.js';
import { createWorkspaceControls } from './workspace-controls.js';
import { createLearningSession } from './learning-session.js';
import { createEvidenceEnvelope, EvidenceRequests, parseDrawing } from './model-evidence.js';
import type { Attempt } from './learning-session.js';
import { lessonContext } from './lesson-beam.js';
import { createPortalPanel, isPortalWorkspace, isCheckedWorkspace, portalStorageKey } from './portal-live.js';
import { boundaryStation, stationLabel } from './load-stations.js';
import { createMomentExercise, portalExercise, exerciseStorage, exerciseStep } from './portal-exercise.js';
let momentExercise: ReturnType<typeof createMomentExercise> | undefined;
const clone = <T>(value: T): T => structuredClone(value);
const id = (prefix: string) => `${prefix}${crypto.randomUUID().slice(0, 6)}`;
renderCourseConventions();
// On a phone the model comes first. Keep the DOM order and keyboard order together.
const narrowWorkspace = matchMedia('(max-width: 750px)');
function arrangeWorkspace() {
    for (const disclosure of document.querySelectorAll<HTMLDetailsElement>('#drawing-toolbox, .exercise-directory, .model-files')) {
        disclosure.open = !narrowWorkspace.matches && (disclosure.id === 'drawing-toolbox' || !document.body.classList.contains('drawing-workspace'));
    }
    const canvas = document.getElementById('canvas')!;
    const toolbar = document.querySelector('.response-toolbar')!;
    const canvasHeader = document.querySelector('.canvas-header')!;
    if (narrowWorkspace.matches) canvas.after(toolbar, canvasHeader);
    else canvas.before(toolbar, canvasHeader);
}
arrangeWorkspace();
narrowWorkspace.addEventListener('change', arrangeWorkspace);
const lesson = lessonContext(location.search);
if (isPortalWorkspace) {
    const exerciseLink = $('portal-exercise-link').querySelector('a')!;
    exerciseLink.href = '../?exercise=portal-absolute-moment#sandbox';
}
const modelStorageKey = portalExercise ? exerciseStorage : isPortalWorkspace ? portalStorageKey : lesson?.storageKey || 'cv2011-model';
if (lesson) {
    $('workspace').insertAdjacentHTML('afterbegin', '<p class="lesson-banner"><a href="learn/beam-basics/">← Back to the beam lesson</a> · Lesson workspace · <a href="./#sandbox">Return to your saved sandbox</a> · <button id="restart-lesson" class="quiet">Restart lesson example</button></p>');
    $('restart-lesson').onclick = () => { commit(() => { model = clone(lesson.model); }); fit(); render(); };
}
let model: Model = portalExercise ? { nodes:[], members:[], supports:[], loads:[] } : isPortalWorkspace ? example('frame') : lesson?.model || example();
try {
    const saved = localStorage.getItem(modelStorageKey);
    if (saved) {
        const candidate = JSON.parse(saved);
        if (isPortalWorkspace) {
            // The numerical diagram engine has its own length/tolerance
            // limits. Exact checker inputs use the strict source schema.
            parseDrawing(candidate);
            model = candidate;
        } else if (analyse(candidate).status !== 'invalid')
            model = candidate;
    }
}
catch { /* Recover from stale browser storage with the default model. */ }
assignLoadLabels(model);
let analysis: Analysis = analyse(model);
let tool = 'select', layer = 'M', mode = 'sandbox', side = 'tension';
let selected: Selection | null = null;
let start: Snap | null = null, hover: Snap | null = null;
let view = { scale: 85, cx: 4, cy: 0 };
let drag: {
    kind: string;
    id?: string;
    before?: Model;
    x: number;
    y: number;
    cx: number;
    cy: number;
} | null = null;
const history: Model[] = [], future: Model[] = [];
let currentMember = isPortalWorkspace ? 'BC' : model.members[0]?.id || '', sectionT = 0.5;
let restoredPortalView = false;
let restoreCheckerControls: (() => void) | undefined;
function preserveCheckerView() {
    sessionStorage.setItem(modelStorageKey + '/view', JSON.stringify({ model: JSON.stringify(model),
        member: currentMember, parameter: sectionT, layer, mode, side, view, selected, tool,
        history, future, solutionStep, solutionRevealed, hintUsed, practiceResultsVisible, practiceView,
        gridSpacing: $<HTMLInputElement>('grid-spacing').value,
        focused: document.querySelector('.work-grid')!.classList.contains('is-focused'),
        checkboxes: Object.fromEntries([...document.querySelectorAll<HTMLInputElement>('input[type=checkbox][id]')]
            .map(input => [input.id, input.checked])) }));
}
if (isCheckedWorkspace) {
    // Activation reloads this page once. Restore its view/query only for the
    // identical saved model; a certificate is always checked afresh.
    const stateKey = modelStorageKey + '/view';
    try {
        const saved = sessionStorage.getItem(stateKey);
        sessionStorage.removeItem(stateKey);
        const state = saved ? JSON.parse(saved) : null;
        if (state?.model === JSON.stringify(model) && model.members.some(member => member.id === state.member)
            && Number.isFinite(state.parameter) && state.parameter >= 0 && state.parameter <= 1
            && ['M', 'V', 'N', 'displacement', 'none'].includes(state.layer)
            && ['sandbox', 'practice', 'insights'].includes(state.mode)
            && ['tension', 'compression'].includes(state.side)
            && Number.isFinite(state.view?.scale) && state.view.scale > 0
            && Number.isFinite(state.view?.cx) && Number.isFinite(state.view?.cy)) {
            currentMember = state.member; sectionT = state.parameter;
            layer = state.layer; mode = state.mode; side = state.side; view = state.view;
            // History contains drawings only; accepted reports are never restored.
            for (const [target, snapshots] of [[history, state.history], [future, state.future]] as const) {
                if (Array.isArray(snapshots) && snapshots.length <= 60) {
                    snapshots.forEach(snapshot => parseDrawing(snapshot));
                    target.push(...snapshots);
                }
            }
            const selectionCollections: Record<string, { id: string }[]> = {
                node: model.nodes, member: model.members, load: model.loads, support: model.supports,
            };
            if (state.selected && selectionCollections[state.selected.type]?.some(item => item.id === state.selected.id))
                selected = { type: state.selected.type, id: state.selected.id };
            if ([...document.querySelectorAll<HTMLElement>('[data-tool]')].some(button => button.dataset.tool === state.tool)) tool = state.tool;
            restoreCheckerControls = () => {
                if (state.practiceView && typeof state.practiceView.answer === 'string' && typeof state.practiceView.units === 'string')
                    practiceView = { ...state.practiceView, pending: false };
                if (state.solutionStep in stepDefinitions) solutionStep = state.solutionStep;
                solutionRevealed = state.solutionRevealed === true;
                hintUsed = state.hintUsed === true;
                practiceResultsVisible = state.practiceResultsVisible === true;
                if (Number(state.gridSpacing) > 0) $<HTMLInputElement>('grid-spacing').value = state.gridSpacing;
                $<HTMLSelectElement>('moment-side').value = side;
                controls.setFocus(state.focused === true);
                controls.showTool(tool);
            };
            for (const [id, checked] of Object.entries(state.checkboxes || {})) {
                const input = document.getElementById(id);
                if (input instanceof HTMLInputElement && input.type === 'checkbox' && typeof checked === 'boolean') input.checked = checked;
            }
            restoredPortalView = true;
        }
    } catch { /* Ignore stale view state; the model has its own recovery above. */ }
    window.addEventListener('beforeunload', preserveCheckerView);
}
let portalPanel: ReturnType<typeof createPortalPanel> | undefined;
let portalSignature = '';
let previewingCut = false;
const evidenceRequests = new EvidenceRequests();
let evidenceRawSource: string | undefined;
const cutSide = (): 'left' | 'right' => sectionT === 0 ? 'right' : sectionT === 1 ? 'left'
    : document.querySelector<HTMLSelectElement>('#frame-side')?.value === 'left' ? 'left' : 'right';
const evidenceQuery = () => ({ member: currentMember, parameter: sectionT, cutSide: cutSide(), quantity: 'section-response', units: 'kN, kN m, m, rad', signConvention: 'global y upward; rotation counterclockwise; tension N positive; sagging M positive; dM/dx = V' });
function updateEvidenceBinding(preview = false) {
    if (isCheckedWorkspace) $<HTMLInputElement>('section-position').value = String(sectionT * 1000);
    try { evidenceRequests.update(model, evidenceQuery()); }
    catch { evidenceRequests.invalidate(); }
    // Render-only changes do not repeatedly launch checks. Mechanical/query
    // changes, including a revert, synchronously remove the previous result.
    const signature = JSON.stringify([model, currentMember, sectionT, cutSide()]);
    if (signature !== portalSignature) {
        portalSignature = signature;
        momentExercise?.bind(signature + ($<HTMLSelectElement>('frame-side')?.value || ''));
        previewingCut = preview;
        portalPanel?.update(currentMember, sectionT, preview);
    }
}
let solutionStep = 'reaction_left', solutionRevealed = false, hintUsed = false, practiceResultsVisible = false;
interface PracticeView { key: string; answer: string; units: string; submission?: string; pending?: boolean }
let practiceView: PracticeView | undefined;
const svg = $('canvas') as unknown as SVGSVGElement;
// Redraw the geometry independently so the cut grip retains keyboard focus
// and pointer capture while inspection updates the free body and checked query.
const geometry = document.createElementNS('http://www.w3.org/2000/svg','g');
svg.append(geometry);
const updateCutGrip = createSandboxCut(svg,(parameter, face, preview) => {
    const nextFace = parameter === 0 ? 'right' : parameter === 1 ? 'left' : face;
    if (parameter === sectionT && nextFace === cutSide()) {
        if (!preview && previewingCut) {
            previewingCut = false;
            portalPanel?.update(currentMember,sectionT);
        }
        return;
    }
    sectionT = parameter;
    $<HTMLSelectElement>('frame-side').value = nextFace;
    render(true,preview);
});
// Shared drawing dimensions keep pointer mapping, fitting and annotations aligned.
let canvasWidth = 1000;
let canvasHeight = 400;
function sizeDrawing() {
    const width = narrowWorkspace.matches && (isDrawingSandbox() || isPortalWorkspace || portalExercise) ? 640 : 1000;
    const height = width === 640 && document.querySelector('.work-grid.is-focused') ? 640 : 400;
    if (width === canvasWidth && height === canvasHeight) return;
    canvasHeight = height;
    // Preserve the visible span and pan centre when the drawing sheet changes width.
    view.scale *= width / canvasWidth;
    canvasWidth = width;
    svg.setAttribute('viewBox', `0 0 ${width} ${canvasHeight}`);
}
svg.setAttribute('viewBox', `0 0 ${canvasWidth} ${canvasHeight}`);
interface Snap {
    x: number;
    y: number;
    node?: string;
    member?: string;
    t?: number;
}
function toast(message: string) { $('toast').textContent = message; $('toast').classList.add('show'); setTimeout(() => $('toast').classList.remove('show'), 4200); }
function checkpoint(before = model) { history.push(clone(before)); if (history.length > 60)
    history.shift(); future.length = 0; }
function changed(keepInspector = false) {
    // Removing the import status above the drawing would shift the pivot
    // beneath an active pointer. Dismiss it once the rotation finishes.
    if (!rotation) $('workspace-operation').hidden = true;
    evidenceRawSource = undefined;
    assignLoadLabels(model);
    updateEvidenceBinding();
    analysis = analyse(model);
    localStorage.setItem(modelStorageKey, JSON.stringify(model));
    render(keepInspector);
}
function editModel(action: () => void, startUndo: boolean, keepInspector: boolean) {
    if (startUndo) checkpoint();
    action();
    solutionRevealed = false;
    hintUsed = false;
    practiceResultsVisible = false;
    changed(keepInspector);
}
function commit(action: () => void) { editModel(action, true, false); }
function screen(point: {
    x: number;
    y: number;
}) { return { x: canvasWidth / 2 + (point.x - view.cx) * view.scale, y: canvasHeight / 2 - (point.y - view.cy) * view.scale }; }
function world(event: PointerEvent | WheelEvent) { const p = new DOMPoint(event.clientX, event.clientY).matrixTransform(svg.getScreenCTM()!.inverse()); return { x: view.cx + (p.x - canvasWidth / 2) / view.scale, y: view.cy - (p.y - canvasHeight / 2) / view.scale }; }
function projection(point: {
    x: number;
    y: number;
}, member: Member) {
    const a = model.nodes.find(n => n.id === member.a)!, b = model.nodes.find(n => n.id === member.b)!;
    const dx = b.x - a.x, dy = b.y - a.y, length = Math.hypot(dx, dy);
    const t = Math.max(0, Math.min(1, ((point.x - a.x) * dx + (point.y - a.y) * dy) / (length * length)));
    const p = { x: a.x + t * dx, y: a.y + t * dy };
    return { ...p, t, distance: Math.hypot(point.x - p.x, point.y - p.y), length };
}
function nearestMember(point: {
    x: number;
    y: number;
}) {
    return model.members.map(member => ({ ...projection(point, member), member: member.id })).sort((a, b) => a.distance - b.distance)[0];
}
function snap(point: {
    x: number;
    y: number;
}, exclude?: string): Snap {
    const enabled = $<HTMLInputElement>('snap').checked, radius = 14 / view.scale;
    if (enabled) {
        const node = model.nodes.filter(n => n.id !== exclude).find(n => Math.hypot(n.x - point.x, n.y - point.y) < radius);
        if (node)
            return { ...node, node: node.id };
        const closest = nearestMember(point);
        if (closest && closest.distance < radius) {
            const grid = Math.max(0.05, Number($<HTMLInputElement>('grid-spacing').value) || 0.5);
            const t = Math.max(0, Math.min(1, Math.round(closest.t * closest.length / grid) * grid / closest.length));
            return { ...position(model, closest.member, t), member: closest.member, t };
        }
        const grid = Math.max(0.05, Number($<HTMLInputElement>('grid-spacing').value) || 0.5);
        return { x: Math.round(point.x / grid) * grid, y: Math.round(point.y / grid) * grid };
    }
    return point;
}
function fit() {
    if (!model.nodes.length) {
        view = { scale: 85, cx: 4, cy: 0 };
        return;
    }
    const xs = model.nodes.map(n => n.x), ys = model.nodes.map(n => n.y);
    const minX = Math.min(...xs), maxX = Math.max(...xs), minY = Math.min(...ys), maxY = Math.max(...ys);
    view = { cx: (minX + maxX) / 2, cy: (minY + maxY) / 2, scale: Math.min(100, (canvasWidth - 240) / Math.max(maxX - minX, 1), (canvasHeight - 200) / Math.max(maxY - minY, 1)) };
}
function ensureNode(point: Snap): string {
    if (point.node)
        return point.node;
    const existing = model.nodes.find(n => Math.hypot(n.x - point.x, n.y - point.y) < 1e-7);
    if (existing)
        return existing.id;
    const nodeId = id('J');
    if (point.member && point.t !== undefined)
        return splitMember(model, point.member, point.t, nodeId);
    model.nodes.push({ id: nodeId, x: point.x, y: point.y });
    return nodeId;
}
function spanPixels(length:number) {
    return length * view.scale * (svg.getScreenCTM()?.a || 1);
}
function loadProjection(point:{x:number;y:number}) {
    const first = start;
    if (!first?.member) return nearestMember(point);
    const owner = model.members.find(m => m.id === first.member)!;
    // At a shared joint the second boundary determines which span is loaded.
    const joint = first.t === 0 ? owner.a : first.t === 1 ? owner.b : undefined;
    const eligible = joint ? model.members.filter(m => m.a === joint || m.b === joint) : [owner];
    return eligible.map(m => ({...projection(point,m),member:m.id})).sort((a,b)=>a.distance-b.distance)[0];
}
function attach(point: {
    x: number;
    y: number;
}) {
    const closest = tool === 'distributed' ? loadProjection(point) : nearestMember(point);
    if (!closest || closest.distance > 30 / view.scale) {
        toast('Place this object on a member.');
        return null;
    }
    let t = closest.t;
    if (tool === 'distributed') {
        t = boundaryStation(t,spanPixels(closest.length),$<HTMLInputElement>('snap').checked);
    } else if ($<HTMLInputElement>('snap').checked) {
        const grid = Number($<HTMLInputElement>('grid-spacing').value) || 0.5;
        t = Math.max(0, Math.min(1, Math.round(t * closest.length / grid) * grid / closest.length));
    }
    return { member: closest.member, t };
}
function drawArrow(x: number, y: number, dx: number, dy: number, color: string, label = '', extra = '') {
    return `<g ${extra}>${forceSymbol(x, y, dx, -dy, color, label, Math.hypot(dx, dy), 0)}</g>`;
}
function supportDrawing(support: Support) {
    const p = screen(position(model, support.member, support.t));
    const member = model.members.find(item => item.id === support.member)!;
    const a = position(model, member.id, 0), b = position(model, member.id, 1);
    const memberAngle = -Math.atan2(b.y - a.y, b.x - a.x) * 180 / Math.PI;
    const rotation = ['roller', 'guided'].includes(support.kind) ? 90 - support.angle : support.kind === 'fixed' ? memberAngle + (support.t === 1 ? 180 : 0) : 0;
    const selectedRing = selected?.id === support.id ? '<circle r="36" fill="none" stroke-dasharray="3 3" opacity=".5"/>' : '';
    const custom = support.kind === 'custom' ? `<text y="29" text-anchor="middle" stroke="none" fill="${courseColors.ink}" font-size="8">${support.fixX ? 'x' : ''}${support.fixY ? 'y' : ''}${support.fixRotation ? 'θ' : ''}</text>` : '';
    return `<g class="clickable" data-object="support" data-id="${escape(support.id)}" transform="translate(${p.x} ${p.y}) rotate(${rotation})" stroke="${courseColors.member}" stroke-width="1.6" fill="none"><title>${escape(support.kind)} ground support</title><circle cy="15" r="25" class="node-hit" stroke="none"/>${selectedRing}${supportShape(support.kind)}${custom}</g>`;
}
let exactPointId: string | undefined;
let rotation: {
    load: Load; pointer: number; offset: number; snap: (raw: number) => number;
    outward: boolean; startX: number; startY: number; changed: boolean;
} | undefined;

function isDrawingSandbox() { return mode === 'sandbox' && document.body.classList.contains('drawing-workspace'); }

function pointHandle(load: Load) {
    const origin = screen(position(model,load.member,load.t));
    const magnitude = Math.hypot(load.fx,load.fy);
    const ux = load.fx/magnitude, uy = -load.fy/magnitude;
    const scale = svg.getScreenCTM()?.a || 1;
    const radius = 22/scale;
    function room(dx: number, dy: number) {
        const x = dx > 0 ? (canvasWidth-radius-origin.x)/dx : dx < 0 ? (radius-origin.x)/dx : Infinity;
        const y = dy > 0 ? (canvasHeight-radius-origin.y)/dy : dy < 0 ? (radius-origin.y)/dy : Infinity;
        return Math.min(x,y);
    }
    // Near a sheet edge the free tip may have more room than the tail. Keep
    // that choice fixed during rotation so the free end follows the pointer.
    const tail = room(-ux,-uy), tip = room(ux,uy);
    const outward = rotation?.load === load ? rotation.outward : tail < 65 && tip > tail;
    const reach = Math.max(12,Math.min(65,outward ? tip : tail));
    const sign = outward ? 1 : -1;
    return {x:origin.x+sign*reach*ux,y:origin.y+sign*reach*uy,reach,outward,radius};
}

/** Keep the annotation touch target clear of the shaft, handle and section marker. */
function placePointCaption(label: SVGTextElement, load: Load, h: ReturnType<typeof pointHandle>) {
    const box = label.getBBox();
    const origin = screen(position(model,load.member,load.t));
    const clearance = 5/(svg.getScreenCTM()?.a || 1);
    const obstacles = [...svg.querySelectorAll<SVGGraphicsElement>('.cut-marker,.cut-face-label,[data-horizontal-reaction] text')]
        .map(element => element.getBBox());
    obstacles.push(new DOMRect(Math.min(origin.x,h.x),Math.min(origin.y,h.y),
        Math.abs(origin.x-h.x),Math.abs(origin.y-h.y)));
    const left = h.x-h.radius-clearance-box.width, right = h.x+h.radius+clearance;
    const above = Math.min(h.y,origin.y)-box.height-clearance, below = Math.max(h.y,origin.y)+clearance;
    const sides = h.x < origin.x ? [left,right] : [right,left];
    const levels = h.y > origin.y ? [below,above] : [above,below];
    let best = {x:0,y:0,score:Infinity};
    for (const x of sides) for (const y of levels) {
        const px = Math.max(clearance, Math.min(x,canvasWidth-box.width-clearance));
        const py = Math.max(clearance, Math.min(y,canvasHeight-box.height-clearance));
        let score = Math.abs(px-x) + Math.abs(py-y);
        for (const blocked of obstacles) {
            const w = Math.min(px+box.width,blocked.x+blocked.width+clearance)-Math.max(px,blocked.x-clearance);
            const ht = Math.min(py+box.height,blocked.y+blocked.height+clearance)-Math.max(py,blocked.y-clearance);
            if (w>0 && ht>0) score += w*ht;
        }
        if (score < best.score) best={x:px,y:py,score};
    }
    label.setAttribute('x',String(Number(label.getAttribute('x'))+best.x-box.x));
    label.setAttribute('y',String(Number(label.getAttribute('y'))+best.y-box.y));
}

function loadDrawing(load: Load) {
    const p = screen(position(model, load.member, load.t));
    const label = loadLabels(model).get(load.id)!;
    const color = courseColors.force;
    const tag = `class="clickable" ${load.kind === 'force' && isDrawingSandbox() ? 'data-point-force' : ''} data-object="load" data-id="${escape(load.id)}"`;
    // Concentric arcs keep each applied couple centred on its attachment.
    const labelBelow = p.y < canvasHeight / 2;
    const preceding = model.loads.slice(0, model.loads.indexOf(load));
    const coupleLane = load.kind === 'moment' ? preceding.filter(other => {
        if (other.kind !== 'moment') return false;
        const origin = screen(position(model, other.member, other.t));
        return Math.hypot(origin.x - p.x, origin.y - p.y) < 1;
    }).length : 0;
    if (load.kind === 'force' && Math.hypot(load.fx, load.fy) < 1e-12 || load.kind === 'moment' && Math.abs(load.mz) < 1e-12)
        return `<g ${tag}><circle cx="${p.x}" cy="${p.y}" r="16" class="node-hit"/><text x="${p.x + 8}" y="${load.kind === 'moment' ? (labelBelow ? p.y + 49 + 10 * coupleLane : p.y - 35 - 10 * coupleLane) : p.y - 15}" dy="${labelBelow ? coupleLane : -coupleLane}em" class="svg-label">${symbolLabel(label)} = 0 ${load.kind === 'force' ? 'kN' : 'kN m'}</text></g>`;
    if (load.kind === 'force') {
        const magnitude = Math.hypot(load.fx, load.fy);
        const handle = selected?.type === 'load' && selected.id === load.id && isDrawingSandbox() ? pointHandle(load) : undefined;
        return `<g ${tag}>${forceSymbol(p.x, p.y, load.fx, load.fy, color, `${label} = ${number(magnitude)} kN`, handle ? handle.reach-5 : 60, 5, handle?.outward)}</g>`;
    }
    if (load.kind === 'moment') {
        return `<g ${tag}>${momentSymbol(p.x, p.y, load.mz, color, `${label} = ${number(Math.abs(load.mz))} kN m`, 25 + 10 * coupleLane, coupleLane, labelBelow)}</g>`;
    }
    const end = screen(position(model, load.member, load.end));
    const dx = end.x - p.x, dy = p.y - end.y;
    const length = Math.hypot(dx, dy);
    const axis = lineLoadAxis(load, dx / length, dy / length);
    const max = Math.max(Math.abs(load.fy), Math.abs(load.qEnd), 1);
    const tail = (point: {x:number; y:number}, intensity: number) =>
        (point.x - axis.x * intensity / max * 53) + ' ' + (point.y + axis.y * intensity / max * 53);
    const envelope = 'M ' + tail(p, load.fy) + ' L ' + tail(end, load.qEnd);
    let result = `<g ${tag}><path class="hit" d="${envelope}"/>`;
    const count = Math.max(3, Math.ceil(Math.hypot(end.x - p.x, end.y - p.y) / 27));
    for (let i = 0; i <= count; i++) {
        const t = i / count, q = load.fy + (load.qEnd - load.fy) * t;
        result += drawArrow(p.x + (end.x - p.x) * t, p.y + (end.y - p.y) * t, axis.x * q / max * 53, -axis.y * q / max * 53, color);
    }
    const endpointLabel = (end: string) => `${label}${label.includes('_') ? ',' : '_'}${end}`;
    const sign = load.direction === undefined ? -1 : 1;
    const axisLabel = load.direction === undefined ? '↓ +' : load.direction === 'member-normal' ? '+local y' : number(load.direction) + '° global';
    const intensityLabel = load.qEnd === load.fy ? `${label} = ${number(sign * load.fy)}` : `${endpointLabel('a')} = ${number(sign * load.fy)} → ${endpointLabel('b')} = ${number(sign * load.qEnd)}`;
    result += `<path d="${envelope}" stroke="${color}" fill="none"/><text class="svg-label" x="${(p.x + end.x) / 2}" y="${Math.min(p.y, end.y) - 67}" text-anchor="middle">${symbolLabel(intensityLabel)} kN/m (${axisLabel})</text></g>`;
    return result;
}
function jointDrawing(node: Point) {
    const p = screen(node), connected = jointConnections(model, node);
    const others = connected.filter(item => item.member.id !== referenceMember(model, node.id));
    const pinned = others.length > 0 && others.every(item => item.rule.axial === 'rigid' && item.rule.transverse === 'rigid' && item.rule.rotation === 'free');
    const semiRigid = others.length > 0 && others.every(item => item.rule.axial === 'rigid' && item.rule.transverse === 'rigid' && typeof item.rule.rotation === 'number');
    let shape = `<circle cx="${p.x}" cy="${p.y}" r="3" fill="${courseColors.member}"/>`;
    if (pinned) shape = `<circle cx="${p.x}" cy="${p.y}" r="5.5" fill="white" stroke="${courseColors.member}" stroke-width="1.6"/>`;
    else if (semiRigid) shape = rotationalSpring(p.x, p.y);
    else for (const { member, end, rule } of others) {
        if (Object.values(rule).every(value => value === 'rigid')) continue;
        const opposite = screen(position(model, member.id, end === 'a' ? 1 : 0));
        const length = Math.hypot(opposite.x - p.x, opposite.y - p.y);
        const q = { x: p.x + (opposite.x - p.x) / length * 19, y: p.y + (opposite.y - p.y) / length * 19 };
        if (rule.axial === 'free' && rule.transverse === 'rigid' && rule.rotation === 'free') {
            const angle = Math.atan2(opposite.y - p.y, opposite.x - p.x) * 180 / Math.PI;
            shape += `<g transform="translate(${q.x} ${q.y}) rotate(${angle})" stroke="${courseColors.member}" stroke-width="1.5"><circle r="4" fill="white"/><path d="M -9 -6 H 9 M -9 6 H 9"/></g>`;
        } else if (typeof rule.rotation === 'number' && rule.axial === 'rigid' && rule.transverse === 'rigid') shape += rotationalSpring(q.x, q.y);
        else if (rule.rotation === 'free' && rule.axial === 'rigid' && rule.transverse === 'rigid') shape += `<circle cx="${q.x}" cy="${q.y}" r="5.5" fill="white" stroke="${courseColors.member}" stroke-width="1.6"/>`;
        else shape += `<path d="M ${q.x} ${q.y - 7} l 7 7 l -7 7 l -7 -7 Z" fill="white" stroke="${courseColors.member}" stroke-width="1.5"/>`;
    }
    // Put labels away from the directions occupied by connected members. This
    // moves only text; the node marker and all applied actions remain anchored.
    const candidates = [{ x: -16, y: -15 }, { x: 16, y: -15 }, { x: 18, y: 19 }, { x: -18, y: 19 }];
    const offset = candidates.sort((a, b) => {
        const score = (candidate: { x: number; y: number }) => connected.reduce((sum, item) => {
            const other = screen(position(model, item.member.id, item.end === 'a' ? 1 : 0));
            const direction = ((other.x - p.x) * candidate.x + (other.y - p.y) * candidate.y) / (Math.hypot(other.x - p.x, other.y - p.y) * Math.hypot(candidate.x, candidate.y));
            return sum + Math.max(0, direction);
        }, 0);
        return score(a) - score(b);
    })[0];
    const title = pinned ? 'Pinned joint' : semiRigid ? 'Semi-rigid joint' : others.some(item => Object.values(item.rule).some(value => value !== 'rigid')) ? 'Joint with member-specific constraints' : 'Rigid joint';
    return `<g class="clickable" data-object="node" data-id="${escape(node.id)}" data-joint-symbol="${pinned ? 'pinned' : semiRigid ? 'semi-rigid' : title === 'Rigid joint' ? 'rigid' : 'custom'}"><title>${title} ${nodeLabels(model).get(node.id)}</title><circle cx="${p.x}" cy="${p.y}" r="13" class="node-hit"/>${shape}${selected?.id === node.id ? `<circle cx="${p.x}" cy="${p.y}" r="15" stroke="${courseColors.force}" fill="none" stroke-dasharray="3 3"/>` : ''}<text x="${p.x + offset.x}" y="${p.y + offset.y}" text-anchor="middle" class="node-label">${nodeLabels(model).get(node.id)}</text></g>`;
}
function responsesVisible() {
    return (mode !== 'practice' || practiceResultsVisible) && (!portalExercise || momentExercise?.visible === true);
}
function renderCanvas() {
    sizeDrawing();
    const diagramNote = $('frame-diagram-note');
    diagramNote.hidden = true;
    if (svg.nextElementSibling !== diagramNote) svg.after(diagramNote);
    const signsExpanded = $('workspace-conventions').querySelector('details')?.open ?? false;
    $('workspace-conventions').innerHTML = workspaceConventions(model, currentMember);
    $('workspace-conventions').querySelector('details')!.open = signsExpanded;
    const grid = Math.max(0.05, Number($<HTMLInputElement>('grid-spacing').value) || 0.5);
    const spacing = grid * view.scale;
    const origin = screen({ x: 0, y: 0 });
    let drawing = `<defs><pattern id="grid" width="${spacing}" height="${spacing}" patternUnits="userSpaceOnUse" x="${origin.x % spacing}" y="${origin.y % spacing}"><circle cx="0" cy="0" r="1" fill="#dce5df"/></pattern></defs><rect width="${canvasWidth}" height="${canvasHeight}" fill="url(#grid)"/>`;
    const all = analysis.elements.flatMap(e => e.samples);
    if (analysis.status === 'stable' && layer !== 'none' && responsesVisible()) {
        if (layer === 'displacement') {
            const maximum = Math.max(...all.map(p => Math.hypot(p.ux, p.uy)), 1e-12), magnification = 55 / (view.scale * maximum);
            for (const element of analysis.elements) {
                const path = element.samples.map((p, i) => { const q = screen({ x: p.x + p.ux * magnification, y: p.y + p.uy * magnification }); return `${i ? 'L' : 'M'} ${q.x} ${q.y}`; }).join(' ');
                drawing += `<path d="${path}" fill="none" stroke="${courseColors.reaction}" stroke-width="2.5"/>`;
            }
            diagramNote.textContent = 'Displacement magnification ×' + number(magnification) + '. Reported displacements are unscaled.';
            diagramNote.hidden = false;
        }
        else {
            const field = layer as 'N' | 'V' | 'M', maximum = Math.max(...all.map(p => Math.abs(p[field])), 1e-10), scale = 70 / maximum;
            for (const element of analysis.elements) {
                const direction = field === 'M' ? (side === 'tension' ? -1 : 1) : 1;
                const points = element.samples.map(p => screen({ x: p.x - element.s * p[field] * scale / view.scale * direction, y: p.y + element.c * p[field] * scale / view.scale * direction }));
                const a = screen(element.samples[0]), b = screen(element.samples.at(-1)!);
                const path = `M ${a.x} ${a.y} ` + points.map(p => `L ${p.x} ${p.y}`).join(' ') + ` L ${b.x} ${b.y} Z`;
                drawing += `<path d="${path}" fill="#087f781c" stroke="#087f78" stroke-width="1.3" pointer-events="none"/>`;
            }
            const section = sectionSample();
            if (section && document.body.classList.contains('drawing-workspace')) {
                const member = model.members.find(item => item.id === currentMember)!;
                const a = position(model, member.id, 0), b = position(model, member.id, 1);
                const length = Math.hypot(b.x - a.x, b.y - a.y);
                const sense = field === 'M' && side === 'tension' ? -1 : 1;
                const offset = section[field] * scale * sense / view.scale;
                const station = position(model, member.id, sectionT);
                const dot = screen({x: station.x - (b.y-a.y)/length*offset, y: station.y + (b.x-a.x)/length*offset});
                drawing += `<circle class="cut-ordinate" data-side="${cutSide()}" cx="${dot.x}" cy="${dot.y}" r="5"><title>Selected ${field} = ${formatSectionResult(section[field])} ${field === 'M' ? 'kN m' : 'kN'}</title></circle>`;
            }
            // Retain the scale note at zero response so a load edit cannot shift the inspector dial.
            if (all.length) {
                const peak = all.reduce((a, b) => Math.abs(a[field]) > Math.abs(b[field]) ? a : b);
                diagramNote.innerHTML = 'Peak ' + math('|' + field + '|=' + quantity(number(Math.abs(peak[field])), field === 'M' ? measureUnits.moment : measureUnits.force)) + ' · Diagram scaled to fit';
                diagramNote.hidden = false;
            }
        }
    }
    for (const member of model.members) {
        const a = screen(position(model, member.id, 0)), b = screen(position(model, member.id, 1));
        drawing += `<g class="clickable" data-object="member" data-id="${escape(member.id)}"><path d="M ${a.x} ${a.y} L ${b.x} ${b.y}" stroke="${courseColors.member}" stroke-width="${selected?.id === member.id ? 6 : 4}" stroke-linecap="round"/><path d="M ${a.x} ${a.y} L ${b.x} ${b.y}" class="hit"/></g>`;
    }
    for (const support of model.supports)
        drawing += supportDrawing(support);
    for (const load of model.loads) {
        if (selected?.type === 'load' && selected.id === load.id && document.body.classList.contains('drawing-workspace')) {
            const attachment = screen(position(model, load.member, load.t));
            drawing += `<circle class="attachment-ring" cx="${attachment.x}" cy="${attachment.y}" r="11" pointer-events="none"/>`;
        }
        drawing += loadDrawing(load);
    }
    for (const node of model.nodes) drawing += jointDrawing(node);
    if ($<HTMLInputElement>('show-reactions').checked && responsesVisible())
        for (const reaction of analysis.reactions) {
            const p = screen(reaction);
            const node = model.nodes.find(node => Math.hypot(node.x - reaction.x, node.y - reaction.y) < 1e-7);
            const label = node ? nodeLabels(model).get(node.id)! : `R${analysis.reactions.indexOf(reaction) + 1}`;
            if (Math.abs(reaction.fy) > 1e-7)
                drawing += `<g pointer-events="none" class="${p.x > canvasWidth * .75 ? 'reaction-label-left' : ''}">${forceSymbol(p.x, p.y, 0, reaction.fy, courseColors.reaction, `${label}ᵧ = ${number(Math.abs(reaction.fy))} kN`, 42, 44)}</g>`;
            if (Math.abs(reaction.fx) > 1e-7)
                drawing += `<g pointer-events="none" data-horizontal-reaction>${forceSymbol(p.x, p.y, reaction.fx, 0, courseColors.reaction, `${label}ₓ = ${number(Math.abs(reaction.fx))} kN`, 42, 20)}</g>`;
            if (Math.abs(reaction.mz) > 1e-7)
                drawing += `<g pointer-events="none" data-moment-reaction>${momentSymbol(p.x, p.y, reaction.mz, courseColors.reaction, `M_${label} = ${number(Math.abs(reaction.mz))} kN m`, 37)}</g>`;
        }
    if (analysis.mechanism)
        for (const motion of analysis.mechanism) {
            const p = screen(motion);
            drawing += `<path class="mechanism" d="M ${p.x} ${p.y} l ${motion.ux * 60} ${-motion.uy * 60}" stroke-width="3"/>`;
        }
    if (currentMember && model.members.some(m => m.id === currentMember) && analysis.status === 'stable') {
        const a = position(model, currentMember, 0), b = position(model, currentMember, 1), p = screen(position(model, currentMember, sectionT));
        const length = Math.hypot(b.x - a.x, b.y - a.y), nx = -(b.y - a.y) / length, ny = -(b.x - a.x) / length;
        drawing += `<path class="cut-marker" d="M ${p.x - nx * 40} ${p.y - ny * 40} L ${p.x + nx * 40} ${p.y + ny * 40}" stroke="#bf7650" stroke-width="1.5" stroke-dasharray="4 4" pointer-events="none"/><circle cx="${p.x}" cy="${p.y}" r="3" fill="#bf7650"/>`;
    }
    if (currentMember && analysis.status === 'stable' && document.body.classList.contains('drawing-workspace')) {
        const p = screen(position(model, currentMember, sectionT));
        drawing += '<text class="cut-face-label" x="' + p.x + '" y="' + (p.y + 58) + '" text-anchor="middle">Cut · ' + cutSide() + '</text>';
    }
    if (start && hover) {
        const a = screen(start), b = screen(hover);
        drawing += `<path d="M ${a.x} ${a.y} L ${b.x} ${b.y}" stroke="#087f78" stroke-width="3" stroke-dasharray="6 5"/><circle cx="${a.x}" cy="${a.y}" r="5" fill="#087f78"/>`;
    }
    if (hover && tool !== 'select') {
        const p = screen(hover);
        drawing += `<circle cx="${p.x}" cy="${p.y}" r="8" fill="none" stroke="#087f78" stroke-width="1.5"/>`;
    }
    if (!model.members.length)
        drawing += `<text x="${canvasWidth / 2}" y="${canvasHeight / 2 - 20}" text-anchor="middle" class="svg-label" style="font-size:23px">Your structure starts here.</text><text x="${canvasWidth / 2}" y="${canvasHeight / 2 + 15}" text-anchor="middle" class="svg-value">Choose Draw member, then its two endpoints.</text>`;
    if (model.members.length && document.body.classList.contains('drawing-workspace')) {
        // The scale bar measures undeformed model length, independently of diagram magnification.
        const metres = 2 ** Math.floor(Math.log2(90 / view.scale));
        const end = canvasWidth - 25, begin = end - metres * view.scale;
        drawing += `<g class="drawing-scale" aria-label="Drawing scale"><path d="M${begin} ${canvasHeight - 34}v6H${end}v-6"/><text x="${(begin + end) / 2}" y="${canvasHeight - 39}" text-anchor="middle">${number(metres)} m</text></g>`;
    }
    geometry.innerHTML = drawing;
    if (selected && document.body.classList.contains('drawing-workspace')) {
        const target = svg.querySelector('[data-object="' + CSS.escape(selected.type) + '"][data-id="' + CSS.escape(selected.id) + '"]');
        target?.classList.add('drawing-selection');
    }
    if (isDrawingSandbox()) {
        const point = selected?.type === 'load' ? model.loads.find(l => l.id === selected?.id && l.kind === 'force') : undefined;
        if (point && Math.hypot(point.fx,point.fy) >= 1e-12) {
            const h = pointHandle(point);
            const caption = svg.querySelector<SVGTextElement>(`[data-point-force][data-id="${CSS.escape(point.id)}"] text`);
            if (caption) placePointCaption(caption,point,h);
            const angle = number(wrap(pointAngle(point)));
            const textX = Math.max(45,Math.min(canvasWidth-45,h.x));
            const textY = h.y > canvasHeight-65 ? h.y-h.radius-8 : h.y+h.radius+21;
            geometry.insertAdjacentHTML('beforeend',`<g data-rotate-force="${escape(point.id)}" class="rotate-handle"><title>Rotate point force</title>
                <circle cx="${h.x}" cy="${h.y}" r="${h.radius}" fill="transparent"/>
                <circle cx="${h.x}" cy="${h.y}" r="${h.radius*.26}" fill="#fffdf6" stroke="${courseColors.force}" stroke-width="2"/>
                </g>${rotation?.changed ? `<text class="rotate-angle svg-value" x="${textX}" y="${textY}" text-anchor="middle" pointer-events="none">${angle}°</text>` : ''}`);
        }
    }
    fitCanvasAnnotations();
    for (const label of svg.querySelectorAll<SVGTextElement>('[data-point-force] text')) {
        const box = label.getBBox();
        const hit = document.createElementNS('http://www.w3.org/2000/svg','rect');
        hit.setAttribute('data-force-annotation','');
        hit.setAttribute('x',String(box.x-2)); hit.setAttribute('y',String(box.y-2));
        hit.setAttribute('width',String(box.width+4)); hit.setAttribute('height',String(box.height+4));
        hit.setAttribute('fill','transparent');
        label.after(hit);
    }
    const member = model.members.find(m => m.id === currentMember);
    const inspect = isDrawingSandbox() && tool === 'select' && analysis.status === 'stable' && member;
    svg.setAttribute('role',inspect ? 'group' : 'img');
    updateCutGrip(inspect ? {
        member:member.id, start:screen(position(model,member.id,0)), end:screen(position(model,member.id,1)),
        parameter:sectionT, face:cutSide(), stations:[0,1,
            ...model.supports.filter(s=>s.member===member.id).map(s=>s.t),
            ...model.loads.filter(l=>l.member===member.id).flatMap(l=>l.kind==='distributed' ? [l.t,l.end] : [l.t])]
    } : undefined);

}

/** Keep labels legible at the canvas edges without moving their force vectors.
 * Measure all labels before writing positions to avoid repeated layout passes.
 */
function fitCanvasAnnotations(): void {
    const bounds = svg.getBoundingClientRect();
    const pixelScale = svg.getScreenCTM()?.a;
    if (!pixelScale || bounds.width === 0) return;
    // On the phone portal sheet use the space outside each column. Keep the
    // caption above its reaction shaft and the base moment beside its arc.
    if (narrowWorkspace.matches && (isPortalWorkspace || portalExercise)) {
        for (const label of svg.querySelectorAll<SVGTextElement>('[data-horizontal-reaction] text')) {
            const vector = label.closest<SVGElement>('[data-vector]')!;
            const x = Number(vector.dataset.originX), left = x <= canvasWidth/2;
            label.setAttribute('text-anchor',left ? 'end' : 'start');
            label.setAttribute('x',String(x + (left ? -38 : 38)));
            label.setAttribute('y',String(Number(vector.dataset.originY)-10));
        }
    }
    const adjustments = Array.from(svg.querySelectorAll<SVGTextElement>('.svg-label, .svg-value')).map(label => {
        const box = label.getBoundingClientRect();
        const shift = box.left < bounds.left + 8 ? bounds.left + 8 - box.left
            : box.right > bounds.right - 8 ? bounds.right - 8 - box.right : 0;
        return { label, shift, left: box.left + shift, right: box.right + shift, top: box.top, bottom: box.bottom };
    });
    const forceLabels = adjustments.filter(({label}) => label.closest('[data-object="load"] [data-vector="force"]'));
    const fixedCaptions = adjustments.filter(({label}) => label.closest('[data-moment-reaction]'));
    const obstacles = [...forceLabels, ...fixedCaptions, ...[...svg.querySelectorAll('.node-label')].map(label=>label.getBoundingClientRect())]
        .sort((a,b)=>b.bottom-a.bottom);
    for (const annotation of adjustments) {
        const {label, shift} = annotation;
        if (shift) label.setAttribute('x', String(Number(label.getAttribute('x')) + shift / pixelScale));
        if (!label.closest('[data-horizontal-reaction]')) continue;
        // When the two text boxes meet, lift only the reaction caption.
        // Keep both force vectors on their original lines of action.
        let bottom = annotation.bottom;
        for (const force of obstacles) {
            if (force.right + 6 <= annotation.left || force.left >= annotation.right + 6) continue;
            const top = bottom - (annotation.bottom - annotation.top);
            if (bottom > force.top - 6 && top < force.bottom + 6) bottom = force.top - 6;
        }
        if (bottom < annotation.bottom) {
            const delta = (bottom - annotation.bottom) / pixelScale;
            const x = Number(label.getAttribute('x')), y = Number(label.getAttribute('y'));
            label.setAttribute('y', String(y + delta));
            if (isPortalWorkspace || portalExercise) {
                const leader = document.createElementNS(svg.namespaceURI,'path');
                leader.setAttribute('d', `M${x} ${y}v${delta + 3}`);
                leader.setAttribute('stroke',courseColors.reaction);
                leader.setAttribute('stroke-width','1');
                label.before(leader);
            }
        }
    }
}
// Re-establish original label anchors after a viewport or font-metric change.
window.addEventListener('resize', renderCanvas);
document.fonts.addEventListener('loadingdone', renderCanvas);
void document.fonts.ready.then(renderCanvas);
function inspector(): void {
    renderInspector({
        container: $('inspector'), model, analysis, selected,
        resultsVisible: responsesVisible(),
        commit, adjustLoad: (edit, first) => editModel(edit, first, true), clearSelection: () => { selected = null; inspector(); },
        removeSelected, projectToMember: projection, notify: toast,
    });
}
function removeSelected() {
    if (!selected)
        return;
    commit(() => {
        if (selected!.type === 'node') {
            const members = model.members.filter(m => m.a === selected!.id || m.b === selected!.id).map(m => m.id);
            model.members = model.members.filter(m => !members.includes(m.id));
            model.loads = model.loads.filter(l => !members.includes(l.member));
            model.supports = model.supports.filter(s => !members.includes(s.member));
            model.nodes = model.nodes.filter(n => n.id !== selected!.id);
        }
        else if (selected!.type === 'member') {
            model.members = model.members.filter(m => m.id !== selected!.id);
            model.loads = model.loads.filter(l => l.member !== selected!.id);
            model.supports = model.supports.filter(s => s.member !== selected!.id);
        }
        else if (selected!.type === 'load')
            model.loads = model.loads.filter(l => l.id !== selected!.id);
        else
            model.supports = model.supports.filter(s => s.id !== selected!.id);
        selected = null;
    });
}
function sectionSample(): Sample | undefined {
    return sampleSection(analysis, currentMember, sectionT, cutSide(), model);
}
function render(keepInspector = false, previewCut = false) {
    const member = model.members.find(m => m.id === currentMember) ?? model.members[0];
    currentMember = member?.id ?? '';
    // The course verifier grades the right-hand limit except at the member end.
    const face = document.querySelector<HTMLSelectElement>('#frame-side');
    if (face) {
        face.disabled = mode === 'practice';
        if (face.disabled) face.value = sectionT === 1 ? 'left' : 'right';
    }
    updateEvidenceBinding(previewCut);
    if (mode === 'practice') {
        const key = JSON.stringify([model, currentMember, sectionT, cutSide(), solutionStep, session.courseId]);
        if (practiceView?.key !== key) {
            practiceView = { key, answer: '', units: stepDefinitions[solutionStep].units };
            practiceResultsVisible = solutionRevealed = hintUsed = false;
        }
    }
    document.body.classList.toggle('practice-predicting', mode === 'practice' && !!problem() && !practiceResultsVisible);
    const section = renderResponses({ model, analysis, currentMember, sectionT, layer, cutSide: cutSide(),
        resultsVisible: responsesVisible() });
    drawingWorkspace.update(model, selected, section.sample, section.stationMath, section.face);
    const fbd = $('section-free-body');
    fbd.hidden = mode !== 'sandbox' || !section.sample;
    $('section-free-body-content').innerHTML = !fbd.hidden && section.sample
        ? sectionFreeBody(model, analysis, currentMember, sectionT, cutSide(), section.sample) : '';
    const checkedScope = document.getElementById('checked-section');
    if (checkedScope) checkedScope.innerHTML = member ? `${escape(memberLabel(model, member))} at ${section.stationMath.join(', ')} (just ${cutSide()})` : 'Choose a member.';
    controls.setHistory(history.length > 0, future.length > 0);
    if (!keepInspector) inspector();
    if (!isDrawingSandbox() || selected?.type !== 'load' || selected.id !== exactPointId) exactPointId = undefined;
    document.body.classList.toggle('point-quick-edit',!!exactPointId);
    $('full-point-properties').hidden = !exactPointId;
    $('edit-selection').hidden = !selected;
    (document.querySelector('.right-panel') as HTMLElement).hidden = !selected;
    $('moment-options').hidden = layer !== 'M';
    renderCanvas();
    if (mode === 'practice')
        renderPractice();
    session.updateStatus();
    if (!isCheckedWorkspace) renderWorked({ model, section: sectionT, practice: mode === 'practice', connected: session.connected,
        request: payload => session.request('/api/worked-solution', payload),
        selectSection: section => {
            sectionT = section;
            $<HTMLInputElement>('section-position').value = String(section * 1000);
            render();
        },
        reveal: () => { solutionRevealed = true; void record('reveal', '', stepDefinitions[solutionStep].units); } });
}
svg.addEventListener('pointerdown', event => {
    if (mode === 'insights')
        return;
    let target = event.target as Element;
    // Touch browsers may retarget a shaft press to the nearby draggable circle.
    // Use the physical contact point to distinguish the two editing gestures.
    if (event.pointerType === 'touch' && isDrawingSandbox()) {
        const contact = document.elementFromPoint(event.clientX,event.clientY);
        if (contact && svg.contains(contact) &&
            (target.closest('[data-rotate-force],[data-point-force]') || contact.closest('[data-rotate-force],[data-point-force]')))
            target = contact;
    }
    const p = world(event), object = target.closest<SVGElement>('[data-object]');
    if (event.button === 1 || event.button === 2) {
        drag = { kind: 'pan', x: event.clientX, y: event.clientY, cx: view.cx, cy: view.cy };
        svg.setPointerCapture(event.pointerId);
        return;
    }
    if (rotation) return;
    const handle = target.closest<SVGElement>('[data-rotate-force]');
    if (handle && isDrawingSandbox() && tool !== 'delete') {
        const load = model.loads.find(load => load.id === handle.dataset.rotateForce)!;
        const origin = position(model,load.member,load.t);
        const raw = Math.atan2(p.y-origin.y,p.x-origin.x)*180/Math.PI;
        const angle = wrap(pointAngle(load));
        rotation = {load,pointer:event.pointerId,offset:angle-raw,snap:angleSnap(angle,true),
            outward:pointHandle(load).outward,startX:event.clientX,startY:event.clientY,changed:false};
        svg.setPointerCapture(event.pointerId);
        event.preventDefault();
        return;
    }
    if (target.closest('[data-force-annotation]') && object && isDrawingSandbox() && (tool === 'select' || selected?.id === object.dataset.id)) {
        exactPointId = object.dataset.id;
        selected = {type:'load',id:exactPointId!};
        controls.setFocus(false);
        render();
        document.querySelector('.inspector-panel')!.scrollIntoView({block:'nearest',behavior:'instant'});
        return;
    }
    exactPointId = undefined;
    if (tool === 'delete' && object) {
        selected = { type: object.dataset.object!, id: object.dataset.id! };
        removeSelected();
        return;
    }
    if (tool === 'select') {
        selected = object ? { type: object.dataset.object!, id: object.dataset.id! } : null;
        if (selected && ['node', 'support', 'load'].includes(selected.type)) {
            drag = { kind: selected.type, id: selected.id, before: clone(model), x: event.clientX, y: event.clientY, cx: view.cx, cy: view.cy };
            svg.setPointerCapture(event.pointerId);
        }
        if (selected?.type === 'member')
            currentMember = selected.id;
        render();
        return;
    }
    if (tool === 'member') {
        const snapped = snap(p);
        if (!start) {
            start = snapped;
            hover = snapped;
            renderCanvas();
            return;
        }
        if (Math.hypot(snapped.x - start.x, snapped.y - start.y) < 0.02) {
            toast('Choose a different end point.');
            return;
        }
        if (start.member && start.member === snapped.member) {
            toast('A member already occupies that span.');
            start = null;
            renderCanvas();
            return;
        }
        commit(() => {
            const a = ensureNode(start!), b = ensureNode(snapped);
            if (model.members.some(m => (m.a === a && m.b === b) || (m.a === b && m.b === a))) {
                toast('A member already connects these joints.');
                return;
            }
            const member = { id: id('M'), a, b, EA: 2000000, EI: 20000 };
            model.members.push(member);
            currentMember = member.id;
        });
        start = null;
        renderCanvas();
        return;
    }
    const attachment = attach(p);
    if (!attachment)
        return;
    if (tool === 'joint') {
        commit(() => {
            const nodeId = ensureNode({ ...position(model, attachment.member, attachment.t), ...attachment });
            selected = { type: 'node', id: nodeId };
        });
        return;
    }
    if (tool === 'distributed') {
        if (!start) {
            start = { ...position(model, attachment.member, attachment.t), ...attachment };
            hover = start;
            renderCanvas();
            return;
        }
        if (start.member !== attachment.member) {
            const owner = model.members.find(m=>m.id===attachment.member)!;
            const first = projection(start,owner);
            if (first.distance > 1e-9) { toast('Choose both load boundaries on the same member.'); return; }
            start = {...position(model,owner.id,first.t),member:owner.id,t:first.t};

        }
        if (Math.abs(start.t! - attachment.t) < 1e-5) {
            toast('Choose a nonzero load interval.');
            return;
        }
        const loadId = id('q');
        const editing = document.body.classList.contains('drawing-workspace');
        commit(() => {
            model.loads.push({ id: loadId, member: attachment.member, kind: 'distributed', t: Math.min(start!.t!, attachment.t), end: Math.max(start!.t!, attachment.t), fx: 0, fy: -5, mz: 0, qEnd: -5 });
            if (editing) selected = { type: 'load', id: loadId };
        });
        const placed = model.loads.find(l => l.id === loadId)!;
        toast('Load stations ' + stationLabel(placed.t) + ' to ' + stationLabel(placed.end) + (editing ? '. Edit the intensities and direction in Properties.' : '. Select the load to edit either boundary.'));
        start = null;
        renderCanvas();
        return;
    }
    commit(() => {
        if (['pin', 'roller', 'fixed', 'guided'].includes(tool)) {
            const existing = model.supports.find(s => s.member === attachment.member && Math.abs(s.t - attachment.t) < 1e-6);
            if (existing) {
                existing.kind = tool as Support['kind'];
                selected = { type: 'support', id: existing.id };
            }
            else {
                const support: Support = { id: id('S'), ...attachment, kind: tool as Support['kind'], angle: 90 };
                model.supports.push(support);
                selected = { type: 'support', id: support.id };
            }
            // Students place both fixed bases consecutively. Keep the drawing
            // surface available until they select an object for editing.
            if (portalExercise && tool === 'fixed') selected = null;
        }
        else {
            const load: Load = { id: id('L'), ...attachment, kind: tool as Load['kind'], end: 1, fx: 0, fy: -20, mz: 20, qEnd: -5 };
            model.loads.push(load);
            selected = { type: 'load', id: load.id };
        }
    });
});
function rotateToPointer(event: PointerEvent) {
    const gesture = rotation;
    if (!gesture || gesture.pointer !== event.pointerId) return;
    if (selected?.id !== gesture.load.id || !model.loads.includes(gesture.load)) { finishRotation(); return; }
    if (!gesture.changed && Math.hypot(event.clientX-gesture.startX,event.clientY-gesture.startY)<3) return;
    const origin = position(model,gesture.load.member,gesture.load.t);
    const p = world(event);
    const dx = p.x-origin.x, dy = p.y-origin.y;
    if (Math.hypot(dx,dy)*view.scale*(svg.getScreenCTM()?.a || 1)<6) return;
    const angle = gesture.snap(Math.atan2(dy,dx)*180/Math.PI + gesture.offset);
    if (Math.abs(wrap(angle-pointAngle(gesture.load)+180)-180)<1e-9) return;
    const first = !gesture.changed;
    gesture.changed = true;
    editModel(() => setPointForce(gesture.load,angle),first,false);
}
svg.addEventListener('pointermove', event => {
    if (rotation) {
        rotateToPointer(event);
        return;
    }
    // Re-rendering the SVG can detach the original pointer target. A released
    // button must end a drag even when the browser omits the expected up event.
    if (drag && event.buttons === 0) {
        endDrag();
    }
    const p = world(event);
    $('coordinates').textContent = `x = ${p.x.toFixed(2)} m, y = ${p.y.toFixed(2)} m`;
    if (drag?.kind === 'pan') {
        const pixelScale = svg.getScreenCTM()!.a;
        view.cx = drag.cx - (event.clientX - drag.x) / (pixelScale * view.scale);
        view.cy = drag.cy + (event.clientY - drag.y) / (pixelScale * view.scale);
        renderCanvas();
        return;
    }
    if (drag) {
        if (drag.kind === 'node') {
            const node = model.nodes.find(n => n.id === drag!.id)!;
            const next = snap(p, node.id);
            node.x = next.x;
            node.y = next.y;
        }
        else {
            const item = (drag.kind === 'support' ? model.supports : model.loads).find(i => i.id === drag!.id)!;
            const member = model.members.find(m => m.id === item.member)!;
            const projected = projection(p, member), step = Number($<HTMLInputElement>('grid-spacing').value) || 0.5;
            let t = $<HTMLInputElement>('snap').checked ? Math.round(projected.t * projected.length / step) * step / projected.length : projected.t;
            t = Math.max(0, Math.min(1, t));
            if ('kind' in item && item.kind === 'distributed') {
                const load = item as Load, width = load.end - load.t;
                t = Math.min(boundaryStation(projected.t, spanPixels(projected.length), $('snap').matches(':checked')), 1 - width);
                load.end = t + width;
            }
            item.t = t;
        }
        analysis = analyse(model);
        render();
        return;
    }
    hover = snap(p);
    if (tool === 'distributed') {
        const near = loadProjection(p);
        if (near && near.distance * view.scale < 30) {
            const t = boundaryStation(near.t,spanPixels(near.length),$<HTMLInputElement>('snap').checked);
            hover = { ...position(model, near.member,t), member:near.member,t };
            $('tool-hint').textContent = (start ? 'Second' : 'First') + ' boundary · station ' + stationLabel(t) + ' of the span (' +
                number(t*near.length) + ' m from the drawn start).';
        }
    }
    if (start || tool !== 'select')
        renderCanvas();
});
function finishRotation(event?: PointerEvent) {
    if (!rotation || (event && rotation.pointer !== event.pointerId)) return;
    const {pointer,changed} = rotation;
    rotation = undefined;
    if (changed) $('workspace-operation').hidden = true;
    if (svg.hasPointerCapture(pointer)) svg.releasePointerCapture(pointer);
    renderCanvas();
}
svg.addEventListener('pointerup',event => { rotateToPointer(event); finishRotation(event); });
svg.addEventListener('pointercancel',finishRotation);
svg.addEventListener('lostpointercapture',finishRotation);
window.addEventListener('blur',() => finishRotation());
function endDrag() {
    const completed = drag;
    drag = null;
    if (completed?.before && JSON.stringify(completed.before) !== JSON.stringify(model)) {
        checkpoint(completed.before);
        solutionRevealed = false;
        practiceResultsVisible = false;
        changed();
    }
}
window.addEventListener('pointerup', endDrag, true);
window.addEventListener('pointercancel', endDrag, true);
window.addEventListener('blur', endDrag);
svg.addEventListener('contextmenu', event => event.preventDefault());
svg.addEventListener('wheel', event => { event.preventDefault(); view.scale = Math.max(10, Math.min(500, view.scale * Math.exp(-event.deltaY * 0.001))); renderCanvas(); }, { passive: false });
function setMode(next: string) {
    mode = ['sandbox', 'practice', 'insights'].includes(next) ? next : 'sandbox';
    location.hash = mode;
    const wasDrawing = document.body.classList.contains('drawing-workspace');
    drawingWorkspace.activate(mode === 'sandbox' && !isPortalWorkspace && !portalExercise);
    if (wasDrawing && !document.body.classList.contains('drawing-workspace')) arrangeWorkspace();
    controls.showMode(mode);
    sizeDrawing();
    const sandboxTitle = portalExercise ? 'Portal frame exercise' : isPortalWorkspace ? 'Checked portal workspace' : 'Structural sandbox';
    $('page-title').textContent = mode === 'sandbox' ? sandboxTitle : mode === 'practice' ? 'Practice problems' : 'Review learning progress';
    $('page-description').innerHTML = mode === 'sandbox' && portalExercise ? `Draw the three-member portal, then predict every location where ${math('|M|')} is greatest on BC.` : mode === 'sandbox' ? 'Draw a structure or open a model to inspect its response.' : mode === 'practice' ? 'Build the model, submit a step, and examine the reasoning.' : 'Review submitted steps and the evidence behind recurring errors.';
    $('page-description').hidden = mode === 'sandbox' && !portalExercise;
    $('practice-panel').hidden = mode !== 'practice';
    $('insights-panel').hidden = mode !== 'insights';
    $('portal-exercise').hidden = !portalExercise || mode === 'insights';
    (document.querySelector('.work-grid') as HTMLElement).hidden = mode === 'insights';
    (document.querySelector('.modelbar') as HTMLElement).hidden = mode === 'insights';
    if (mode === 'insights') void session.renderInsights();
    else render();
}
window.addEventListener('hashchange', () => { if (location.hash.slice(1) !== mode)
    setMode(location.hash.slice(1)); });
$<HTMLSelectElement>('moment-side').onchange = () => { side = $<HTMLSelectElement>('moment-side').value; renderCanvas(); };
$<HTMLInputElement>('show-reactions').onchange = renderCanvas;
$<HTMLInputElement>('grid-spacing').onchange = renderCanvas;
$('zoom-in').onclick = () => { view.scale = Math.min(500, view.scale * 1.25); renderCanvas(); };
$('zoom-out').onclick = () => { view.scale = Math.max(10, view.scale / 1.25); renderCanvas(); };
$('fit').onclick = () => { fit(); renderCanvas(); };
$('focus-workspace').onclick = () => {
    controls.setFocus($('focus-workspace').getAttribute('aria-pressed') !== 'true');
    renderCanvas();
};
$('full-point-properties').onclick = () => {
    exactPointId = undefined;
    render();
    document.querySelector<SVGSVGElement>('.direction-dial')?.focus({preventScroll:true});
};
$('close-inspector').onclick = () => {
    selected = null;
    render();
    document.getElementById('drawing-object')?.focus({ preventScroll: true });
};
$('help-button').onclick = () => $<HTMLDialogElement>('workspace-help').showModal();
$('edit-selection').onclick = () => {
    controls.setFocus(false);
    document.querySelector('.inspector-panel')!.scrollIntoView({ behavior: 'smooth', block: 'start' });
};
$('undo').onclick = () => { if (!history.length)
    return; future.push(clone(model)); model = history.pop()!; selected = null; start = null; changed(); };
$('redo').onclick = () => { if (!future.length)
    return; history.push(clone(model)); model = future.pop()!; selected = null; changed(); };
document.addEventListener('keydown', event => { if ($('workspace').inert || (event.target as HTMLElement).matches('input,select,textarea'))
    return; if (event.key === 'Escape') {
    start = null;
    drag = null;
    controls.setFocus(false);
    renderCanvas();
} if (event.key === 'Delete')
    removeSelected(); if ((event.ctrlKey || event.metaKey) && event.key === 'z') {
    event.preventDefault();
    $('undo').click();
} if ((event.ctrlKey || event.metaKey) && event.key === 'y') {
    event.preventDefault();
    $('redo').click();
} });
$('load-preset').onclick = () => commit(() => { const preset = $<HTMLSelectElement>('preset').value; model = preset === 'empty' ? { nodes: [], members: [], supports: [], loads: [] } : example(preset); selected = null; start = null; currentMember = model.members[0]?.id || ''; fit(); });
$<HTMLSelectElement>('section-member').onchange = () => { currentMember = $<HTMLSelectElement>('section-member').value; updateEvidenceBinding(); render(); };
const stationSlider = $<HTMLInputElement>('section-position');
// Pointer movement uses 1000 steps. An exact typed station can lie between them.
stationSlider.oninput = () => {
    sectionT = Math.round(stationSlider.valueAsNumber) / 1000;
    render();
};
$('export-model').onclick = () => download('cv2011-model.json', { version: model.loads.some(load => load.direction !== undefined) ? 3 : 2, model });
$('export-evidence').onclick = async () => {
    try {
        updateEvidenceBinding();
        const token = evidenceRequests.begin();
        const displayAtStart = JSON.stringify(model.loads.map(load => [load.id, load.label ?? null]));
        const rawAtStart = evidenceRawSource;
        const envelope = await createEvidenceEnvelope(model, evidenceQuery(), rawAtStart);
        if (!evidenceRequests.isCurrent(token) || rawAtStart !== evidenceRawSource || displayAtStart !== JSON.stringify(model.loads.map(load => [load.id, load.label ?? null]))) throw Error('The drawing or query changed; save a fresh snapshot.');
        download('cv2011-evidence-snapshot.json', envelope);
    } catch (error) { toast(`Could not save evidence snapshot: ${String(error)}`); }
};
$('import-model').onclick = () => $('model-file').click();
const modelFile = $<HTMLInputElement>('model-file');
let importRevision = 0;

async function openSelectedModel() {
    const file = modelFile.files?.[0];
    if (!file) return;
    const revision = ++importRevision;
    // Capture the File before clearing the picker so selecting it again retries the read.
    modelFile.value = '';
    setWorkspaceBusy(true, `Opening ${file.name}…`);
    try {
        if (file.size > 100000) throw Error('Model file is too large.');
        const source = await file.text();
        if (revision !== importRevision) return;
        const parsed = JSON.parse(source), candidate = parsed.model || parsed;
        if (parsed.version && parsed.version > 3) throw Error('This model uses a newer file format. Update Structural Explorer before opening it.');
        const checked = analyse(candidate);
        if (checked.status === 'invalid') {
            if (!isPortalWorkspace) throw Error(checked.message);
            parseDrawing(candidate);
        }
        commit(() => { model = candidate; selected = null; start = null; fit(); });
        try {
            if (JSON.stringify(parseDrawing(JSON.parse(source))) === JSON.stringify(parseDrawing(model))) evidenceRawSource = source;
        } catch { /* The ordinary importer accepts drawings outside the strict snapshot schema. */ }
        const member = model.members.find(item => item.id === currentMember);
        let geometry = '';
        if (member) {
            const a = position(model, member.id, 0), b = position(model, member.id, 1);
            geometry = ` ${member.id}: ${member.a} (${a.x}, ${a.y}) to ${member.b} (${b.x}, ${b.y}) m.`;
        }
        setWorkspaceBusy(false, `Opened ${file.name}.${geometry}`);
    } catch (error) {
        if (revision !== importRevision) return;
        setWorkspaceBusy(false, `Could not open ${file.name}. ${String(error)}`);
        toast(`Could not open model: ${String(error)}`);
    }
}
// Guided derivations currently cover a single horizontal, prismatic beam with
// one pin and one vertical roller. The sandbox accepts a wider model class.
function problem() {
    if (model.loads.some(load => load.direction !== undefined)) return null;
    if (model.members.length !== 1 || model.supports.length !== 2 || analysis.status !== 'stable')
        return null;
    const member = model.members[0], a = position(model, member.id, 0), b = position(model, member.id, 1);
    if (Math.abs(a.y - b.y) > 1e-8 || b.x <= a.x)
        return null;
    if (model.supports.filter(s => s.kind === 'pin').length !== 1 || model.supports.filter(s => s.kind === 'roller' && Math.abs(s.angle - 90) < 1e-8).length !== 1)
        return null;
    const supports = [...model.supports].sort((x, y) => x.t - y.t);
    if (supports[1].t - supports[0].t < 1e-6)
        return null;
    const reactions = [...analysis.reactions].sort((x, y) => x.x - y.x), length = b.x - a.x;
    const sample = sectionSample();
    if (!sample)
        return null;
    const left = reactions[0], right = reactions[1];
    return { left, right, length, section: sectionT * length, N: sample.N, V: sample.V, M: sample.M, deflection: sample.uy * 1000, supports };
}
const stepDefinitions: Record<string, {
    title: string;
    units: string;
    hint: string;
}> = {
    reaction_left: { title: 'Left vertical reaction', units: 'kN', hint: 'Take moments about the right support. Include each distributed-load resultant at its centroid and every applied couple.' },
    reaction_right: { title: 'Right vertical reaction', units: 'kN', hint: 'Take moments about the left support. Use the distance between supports, which can differ from the beam length.' },
    normal: { title: 'Normal force at the cut', units: 'kN', hint: 'Isolate the left segment. Positive normal force acts away from the cut. Resolve all horizontal forces on this segment.' },
    shear: { title: 'Shear force at the cut', units: 'kN', hint: 'For a left segment, positive shear acts downward at its right cut. Include only the portion of each distributed load to the left of the cut.' },
    moment: { title: 'Moment at the cut', units: 'kN m', hint: 'Sum moments about the cut. Keep every load at its own lever arm. A positive applied couple contributes a negative jump in the sagging-positive moment diagram.' },
    deflection: { title: `Global vertical displacement ${math('u_y')} at the cut (upward +)`, units: 'mm', hint: `Integrate the moment equation ${math("EI\\,v''=M")} twice on each interval. Apply the displacement boundary conditions at both supports and continuity of displacement ${math('v')} and physical slope ${math("\\theta=v'")} at each continuous section. On this rightward horizontal beam, ${math('u_y=v')}. If using downward-positive virtual-work displacement ${math('\\Delta')}, enter ${math('u_y=-\\Delta')}.` },
};
function renderPractice() {
    const p = problem(), panel = $('practice-panel');
    if (!p) {
        panel.innerHTML = '<div class="panel-label">GUIDED SOLUTIONS</div><h2>Choose a supported beam problem</h2><p>Verified step checks in this release cover one horizontal member drawn left to right, one pin, and one vertical roller. Supports may lie inside the beam. Point forces, couples, and linearly varying distributed loads are supported. Use the sandbox for rigid-jointed frames.</p>';
        return;
    }
    const step = stepDefinitions[solutionStep];
    const view = practiceView!;
    const attempt = view.submission ? session.practiceAttempt(view.submission) : undefined;
    const questions = Object.keys(stepDefinitions);
    const options = questions.map((key, i) => {
        const title = key === 'deflection' ? 'Vertical displacement at the cut' : stepDefinitions[key].title;
        return `<option value="${key}" ${key === solutionStep ? 'selected' : ''}>${i + 1}. ${title}</option>`;
    }).join('');
    const result = attempt?.result;
    const grade = !attempt?.synced ? 'Saved on this device · awaiting verification' :
        result?.status === 'correct' ? 'Correct' : result?.status === 'incorrect' ? 'Check your prediction' : 'Verifier could not grade this expression';
    const unitLabel = (u: string) => u.replace(' m', '·m');
    const feedback = attempt ? `<div class="feedback" id="step-feedback" tabindex="-1" role="status"><strong>Your prediction: ${escape(attempt.answer)} ${escape(unitLabel(attempt.units))}</strong><p>${grade}</p>${attempt.synced && result ? '<p>' + escape(result.message) + '</p>' : ''}</div>` : '';
    const entry = `<form id="practice-entry"><label for="answer">Your prediction</label><div class="answer-row"><input id="answer" required placeholder="Value or expression"><select id="answer-units" aria-label="Answer units">${['kN','N','kN m','N m','mm','m'].map(u => `<option value="${u}">${unitLabel(u)}</option>`).join('')}</select></div><button class="primary" id="check-answer" ${view.pending ? 'disabled' : ''}>Submit prediction</button></form>`;
    const solution = practiceResultsVisible ? `<section aria-label="Worked solution"><h3>Calculated answer</h3><strong>${number(expectedValue(p), 5)} ${unitLabel(step.units)}</strong><p>${step.hint}</p><p class="small">This numerical value comes from the current drawing. The worked panel gives the scope of the structural model check.</p></section>` : '';
    panel.innerHTML = `<label for="practice-step">Practice question</label><select id="practice-step">${options}</select><h2>${step.title}</h2><p>Cut at ${math('x = ' + quantity(number(p.section), measureUnits.length))} from the member start. ${['normal','shear','moment'].includes(solutionStep) ? 'Use the right-hand limit at an interior point action.' : 'Upward is positive.'}</p>${feedback}${attempt ? '' : entry}${solution}
        ${!attempt && !hintUsed ? '<button id="hint">Hint</button>' : ''}
        ${hintUsed && !practiceResultsVisible ? '<p class="feedback">' + step.hint + '</p>' : ''}
        ${attempt && !practiceResultsVisible ? '<button class="primary" id="reveal">Show worked solution</button>' : ''}
        ${attempt ? '<button id="practice-retry">Revise prediction</button>' : ''}
        <details><summary>How this prediction is checked</summary><p>The course verifier grades your expression and units. Offline submissions stay in this browser until you connect and sync them from Insights.</p></details>`;
    const selector = $<HTMLSelectElement>('practice-step');
    selector.onchange = () => { solutionStep = selector.value; render(); $('practice-step').focus(); };
    if (attempt) {
        $('practice-retry').onclick = () => {
            view.submission = undefined;
            practiceResultsVisible = false;
            render(); $('answer').focus();
        };
        if (!practiceResultsVisible) $('reveal').onclick = async () => {
            practiceResultsVisible = solutionRevealed = true;
            const recorded = record('reveal', '', step.units);
            render();
            $('step-feedback').focus();
            // Activating the checker can reload the page. Finish recording this
            // reveal first, and abandon generation if the learner moved on.
            await recorded;
            if (practiceView !== view || mode !== 'practice' || !practiceResultsVisible) return;
            if (isCheckedWorkspace) document.getElementById('frame-generate')?.click();
            else if (session.connected) showWorkedSolution(solutionStep === 'deflection' ? 'integration' : 'sections');
        };
        return;
    }
    const answer = $<HTMLInputElement>('answer'), units = $<HTMLSelectElement>('answer-units');
    answer.value = view.answer; units.value = view.units;
    answer.oninput = () => { view.answer = answer.value; };
    units.onchange = () => { view.units = units.value; };
    if (!hintUsed) $('hint').onclick = () => {
        hintUsed = true; void record('hint', '', step.units); renderPractice(); $('answer').focus();
    };
    $<HTMLFormElement>('practice-entry').onsubmit = async event => {
        event.preventDefault();
        if (view.pending || !answer.value.trim()) return;
        view.answer = answer.value.trim(); view.units = units.value; view.pending = true;
        $<HTMLButtonElement>('check-answer').disabled = true;
        const saved = await record('submit', view.answer, view.units);
        view.pending = false; view.submission = saved.id;
        if (practiceView === view && mode === 'practice') { renderPractice(); $('step-feedback').focus(); }
    };
}
function expectedValue(p: NonNullable<ReturnType<typeof problem>>) { return { reaction_left: p.left.fy, reaction_right: p.right.fy, normal: p.N, shear: p.V, moment: p.M, deflection: p.deflection }[solutionStep]!; }
function record(event: string, answer: string, units: string): Promise<Attempt> {
    return session.record({ model, section: sectionT, step: solutionStep, side, hintUsed,
        solutionRevealed: solutionRevealed || practiceResultsVisible }, event, answer, units);
}
// Components bind once. Model edits and navigation still share this controller.
const drawingWorkspace = createDrawingWorkspace(object => {
    tool = 'select';
    controls.showTool(tool);
    $('tool-hint').textContent = 'Select an object to edit. Drag to move.';
    start = null;
    selected = object;
    if (object?.type === 'member') currentMember = object.id;
    render();
});
const controls = createWorkspaceControls({
    selectTool: next => {
        tool = next; start = null;
        // The floating inspector belongs to the previous selection. Clear it
        // before placing a new object so it cannot intercept the target click.
        if (next !== 'select' && selected) { selected = null; render(); }
        else renderCanvas();
    },
    selectLayer: next => { layer = next; render(); },
    selectMode: setMode,
});
const session = createLearningSession({ notify: toast, onConnectionChange: render });
if (portalExercise) {
    $('portal-exercise-link').hidden = true;
    $('portal-exercise').hidden = false;
    momentExercise = createMomentExercise(() => model, member => {
        currentMember = member; sectionT = 0.5; render();
    }, render, () => session.portalHistory(model), boundaries => commit(() => {
        Object.assign(model.loads[0],boundaries);
    }), (event, answer, assisted) => {
        void session.record({model, section:sectionT, step:exerciseStep, side:'BC', hintUsed:false,
            solutionRevealed:assisted},event,answer,'m');
    });
}
restoreCheckerControls?.();
portalPanel = createPortalPanel(() => model, value => commit(() => {
    if (model.loads.length === 1) { model.loads[0].fy = value; model.loads[0].qEnd = value; }
}), value => { sectionT = value; render(); }, modelStorageKey, preserveCheckerView, (drawing, member, rows) => momentExercise?.checked(drawing,member,rows), message => momentExercise?.status(message));

if (!restoredPortalView) fit();
controls.showLayer(layer);
setMode(location.hash.slice(1) || (restoredPortalView ? mode : 'sandbox'));
modelFile.onchange = openSelectedModel;
if (modelFile.files?.length) void openSelectedModel();
else setWorkspaceBusy(false);
void session.connect();
