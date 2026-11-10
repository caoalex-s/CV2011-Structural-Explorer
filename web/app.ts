/** Workspace controller: model/history ownership, pointer interaction, and canvas drawing.
 * Presentation is delegated to inspector.ts, responses.ts, workspace-controls.ts,
 * and worked.ts. learning-session.ts owns connection settings and submitted records.
 * New lesson pages can supply models through this boundary without changing engine.ts.
 */
import { analyse, example, position, splitMember, nodeLabels, referenceMember } from './engine.js';
import type { Model, Analysis, Point, Member, Support, Load, Sample } from './engine.js';
import { courseColors, forceSymbol, momentSymbol, rotationalSpring, supportShape, symbolLabel } from './symbols.js';
import { renderWorked, showWorkedSolution } from './worked.js';
import { renderCourseConventions } from './course.js';
import { assignLoadLabels, loadLabels } from './load-labels.js';
import { workspaceConventions } from './axes.js';
import { element as $, escapeHtml as escape, formatNumber as number, downloadJson as download } from './ui.js';
import { jointConnections } from './model-view.js';
import type { Selection } from './model-view.js';
import { renderInspector } from './inspector.js';
import { renderResponses, sampleSection } from './responses.js';
import { createWorkspaceControls } from './workspace-controls.js';
import { createLearningSession } from './learning-session.js';
import { createEvidenceEnvelope, EvidenceRequests, parseEvidenceModel } from './model-evidence.js';
import type { Attempt } from './learning-session.js';
import { lessonContext } from './lesson-beam.js';
import { createPortalPanel, isPortalWorkspace, portalStorageKey } from './portal-live.js';
const clone = <T>(value: T): T => structuredClone(value);
const id = (prefix: string) => `${prefix}${crypto.randomUUID().slice(0, 6)}`;
renderCourseConventions();
const lesson = lessonContext(location.search);
const modelStorageKey = isPortalWorkspace ? portalStorageKey : lesson?.storageKey || 'cv2011-model';
if (lesson) {
    $('workspace').insertAdjacentHTML('afterbegin', '<p class="lesson-banner"><a href="learn/beam-basics/">← Back to the beam lesson</a> · Lesson workspace · <a href="./#sandbox">Return to your saved sandbox</a> · <button id="restart-lesson" class="quiet">Restart lesson example</button></p>');
    $('restart-lesson').onclick = () => { commit(() => { model = clone(lesson.model); }); fit(); render(); };
}
let model: Model = isPortalWorkspace ? example('frame') : lesson?.model || example();
try {
    const saved = localStorage.getItem(modelStorageKey);
    if (saved) {
        const candidate = JSON.parse(saved);
        if (analyse(candidate).status !== 'invalid')
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
if (isPortalWorkspace) {
    // Activation reloads this page once. Restore its view/query only for the
    // identical saved model; a certificate is always checked afresh.
    const stateKey = portalStorageKey + '/view';
    try {
        const saved = sessionStorage.getItem(stateKey);
        sessionStorage.removeItem(stateKey);
        const state = saved ? JSON.parse(saved) : null;
        if (state?.model === JSON.stringify(model) && model.members.some(member => member.id === state.member)
            && Number.isFinite(state.parameter) && state.parameter >= 0 && state.parameter <= 1) {
            currentMember = state.member; sectionT = state.parameter;
            layer = state.layer; mode = state.mode; side = state.side; view = state.view;
        }
    } catch { /* Ignore stale view state; the model has its own recovery above. */ }
    window.addEventListener('beforeunload', () => {
        sessionStorage.setItem(stateKey, JSON.stringify({ model: JSON.stringify(model),
            member: currentMember, parameter: sectionT, layer, mode, side, view }));
    });
}
let portalPanel: ReturnType<typeof createPortalPanel> | undefined;
let portalSignature = '';
const evidenceRequests = new EvidenceRequests();
let evidenceRawSource: string | undefined;
const evidenceQuery = () => ({ member: currentMember, parameter: sectionT, cutSide: 'unspecified' as const, quantity: 'section-response', units: 'kN, kN m, m, rad', signConvention: 'global y upward; rotation counterclockwise; tension N positive; sagging M positive; dM/dx = V' });
function updateEvidenceBinding() {
    try { evidenceRequests.update(model, evidenceQuery()); }
    catch { evidenceRequests.invalidate(); }
    // Render-only changes do not repeatedly launch checks. Mechanical/query
    // changes, including a revert, synchronously remove the previous result.
    const signature = JSON.stringify([model, currentMember, sectionT]);
    if (signature !== portalSignature) {
        portalSignature = signature;
        portalPanel?.update(currentMember, sectionT);
    }
}
let solutionStep = 'reaction_left', solutionRevealed = false, hintUsed = false, practiceResultsVisible = false;
let proofStatus = { lean: 'pending', scope: 'Scaled reaction equilibrium identities and plotting-side inversion.' };
const svg = $('canvas') as unknown as SVGSVGElement;
// Shared drawing dimensions keep pointer mapping, fitting and annotations aligned.
const canvasWidth = 1000, canvasHeight = 400;
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
function changed() { evidenceRawSource = undefined; assignLoadLabels(model); updateEvidenceBinding(); analysis = analyse(model); localStorage.setItem(modelStorageKey, JSON.stringify(model)); render(); }
function commit(action: () => void) { checkpoint(); action(); solutionRevealed = false; hintUsed = false; practiceResultsVisible = false; changed(); }
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
function attach(point: {
    x: number;
    y: number;
}) {
    const closest = nearestMember(point);
    if (!closest || closest.distance > 30 / view.scale) {
        toast('Place this object on a member.');
        return null;
    }
    let t = closest.t;
    if ($<HTMLInputElement>('snap').checked) {
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
function loadDrawing(load: Load) {
    const p = screen(position(model, load.member, load.t));
    const label = loadLabels(model).get(load.id)!;
    const color = courseColors.force;
    const tag = `class="clickable" data-object="load" data-id="${escape(load.id)}"`;
    if (load.kind === 'force' && Math.hypot(load.fx, load.fy) < 1e-12 || load.kind === 'moment' && Math.abs(load.mz) < 1e-12)
        return `<g ${tag}><circle cx="${p.x}" cy="${p.y}" r="16" class="node-hit"/><text x="${p.x + 8}" y="${p.y - 15}" class="svg-label">${symbolLabel(label)} = 0 ${load.kind === 'force' ? 'kN' : 'kN m'}</text></g>`;
    if (load.kind === 'force') {
        const magnitude = Math.hypot(load.fx, load.fy);
        return `<g ${tag}>${forceSymbol(p.x, p.y, load.fx, load.fy, color, `${label} = ${number(magnitude)} kN`)}</g>`;
    }
    if (load.kind === 'moment') {
        return `<g ${tag}>${momentSymbol(p.x, p.y, load.mz, color, `${label} = ${number(Math.abs(load.mz))} kN m`)}</g>`;
    }
    const end = screen(position(model, load.member, load.end));
    const max = Math.max(Math.abs(load.fy), Math.abs(load.qEnd), 1);
    let result = `<g ${tag}><path class="hit" d="M ${p.x} ${p.y + load.fy / max * 53} L ${end.x} ${end.y + load.qEnd / max * 53}"/>`;
    const count = Math.max(3, Math.ceil(Math.hypot(end.x - p.x, end.y - p.y) / 27));
    for (let i = 0; i <= count; i++) {
        const t = i / count, q = load.fy + (load.qEnd - load.fy) * t;
        result += drawArrow(p.x + (end.x - p.x) * t, p.y + (end.y - p.y) * t, 0, -q / max * 53, color);
    }
    const endpointLabel = (end: string) => `${label}${label.includes('_') ? ',' : '_'}${end}`;
    const intensityLabel = load.qEnd === load.fy ? `${label} = ${number(-load.fy)}` : `${endpointLabel('a')} = ${number(-load.fy)} → ${endpointLabel('b')} = ${number(-load.qEnd)}`;
    result += `<path d="M ${p.x} ${p.y + load.fy / max * 53} L ${end.x} ${end.y + load.qEnd / max * 53}" stroke="${color}" fill="none"/><text class="svg-label" x="${(p.x + end.x) / 2}" y="${Math.min(p.y, end.y) - 67}" text-anchor="middle">${symbolLabel(intensityLabel)} kN/m (↓ +)</text></g>`;
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
function renderCanvas() {
    const signsExpanded = $('workspace-conventions').querySelector('details')?.open ?? false;
    $('workspace-conventions').innerHTML = workspaceConventions(model, currentMember);
    $('workspace-conventions').querySelector('details')!.open = signsExpanded;
    const grid = Math.max(0.05, Number($<HTMLInputElement>('grid-spacing').value) || 0.5);
    const spacing = grid * view.scale;
    const origin = screen({ x: 0, y: 0 });
    let drawing = `<defs><pattern id="grid" width="${spacing}" height="${spacing}" patternUnits="userSpaceOnUse" x="${origin.x % spacing}" y="${origin.y % spacing}"><circle cx="0" cy="0" r="1" fill="#dce5df"/></pattern></defs><rect width="1000" height="400" fill="url(#grid)"/>`;
    const all = analysis.elements.flatMap(e => e.samples);
    if (analysis.status === 'stable' && layer !== 'none' && (mode !== 'practice' || practiceResultsVisible)) {
        if (layer === 'displacement') {
            const maximum = Math.max(...all.map(p => Math.hypot(p.ux, p.uy)), 1e-12), magnification = 55 / (view.scale * maximum);
            for (const element of analysis.elements) {
                const path = element.samples.map((p, i) => { const q = screen({ x: p.x + p.ux * magnification, y: p.y + p.uy * magnification }); return `${i ? 'L' : 'M'} ${q.x} ${q.y}`; }).join(' ');
                drawing += `<path d="${path}" fill="none" stroke="${courseColors.reaction}" stroke-width="2.5"/>`;
            }
            drawing += `<text x="22" y="375" class="svg-value">Displacement magnification ×${number(magnification)} · values are unscaled</text>`;
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
            if (maximum > 1e-8) {
                const peak = all.reduce((a, b) => Math.abs(a[field]) > Math.abs(b[field]) ? a : b);
                drawing += `<text x="22" y="375" class="svg-value">${symbolLabel(`Peak |${field}| = ${number(Math.abs(peak[field]))} ${field === 'M' ? 'kN m' : 'kN'} · diagrams scaled to fit`)}</text>`;
            }
        }
    }
    for (const member of model.members) {
        const a = screen(position(model, member.id, 0)), b = screen(position(model, member.id, 1));
        drawing += `<g class="clickable" data-object="member" data-id="${escape(member.id)}"><path d="M ${a.x} ${a.y} L ${b.x} ${b.y}" stroke="${courseColors.member}" stroke-width="${selected?.id === member.id ? 6 : 4}" stroke-linecap="round"/><path d="M ${a.x} ${a.y} L ${b.x} ${b.y}" class="hit"/></g>`;
    }
    for (const support of model.supports)
        drawing += supportDrawing(support);
    for (const load of model.loads)
        drawing += loadDrawing(load);
    for (const node of model.nodes) drawing += jointDrawing(node);
    if ($<HTMLInputElement>('show-reactions').checked && (mode !== 'practice' || practiceResultsVisible))
        for (const reaction of analysis.reactions) {
            const p = screen(reaction);
            const node = model.nodes.find(node => Math.hypot(node.x - reaction.x, node.y - reaction.y) < 1e-7);
            const label = node ? nodeLabels(model).get(node.id)! : `R${analysis.reactions.indexOf(reaction) + 1}`;
            if (Math.abs(reaction.fy) > 1e-7)
                drawing += `<g pointer-events="none" class="${p.x > canvasWidth * .75 ? 'reaction-label-left' : ''}">${forceSymbol(p.x, p.y, 0, reaction.fy, courseColors.reaction, `${label}ᵧ = ${number(Math.abs(reaction.fy))} kN`, 42, 44)}</g>`;
            if (Math.abs(reaction.fx) > 1e-7)
                drawing += `<g pointer-events="none">${forceSymbol(p.x, p.y, reaction.fx, 0, courseColors.reaction, `${label}ₓ = ${number(Math.abs(reaction.fx))} kN`, 42, 20)}</g>`;
            if (Math.abs(reaction.mz) > 1e-7)
                drawing += `<g pointer-events="none">${momentSymbol(p.x, p.y, reaction.mz, courseColors.reaction, `M(${label}) = ${number(Math.abs(reaction.mz))} kN m`, 37)}</g>`;
        }
    if (analysis.mechanism)
        for (const motion of analysis.mechanism) {
            const p = screen(motion);
            drawing += `<path class="mechanism" d="M ${p.x} ${p.y} l ${motion.ux * 60} ${-motion.uy * 60}" stroke-width="3"/>`;
        }
    if (currentMember && model.members.some(m => m.id === currentMember) && analysis.status === 'stable') {
        const a = position(model, currentMember, 0), b = position(model, currentMember, 1), p = screen(position(model, currentMember, sectionT));
        const length = Math.hypot(b.x - a.x, b.y - a.y), nx = -(b.y - a.y) / length, ny = -(b.x - a.x) / length;
        drawing += `<path d="M ${p.x - nx * 40} ${p.y - ny * 40} L ${p.x + nx * 40} ${p.y + ny * 40}" stroke="#bf7650" stroke-width="1.5" stroke-dasharray="4 4" pointer-events="none"/><circle cx="${p.x}" cy="${p.y}" r="3" fill="#bf7650"/>`;
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
        drawing += `<text x="500" y="180" text-anchor="middle" class="svg-label" style="font-size:23px">Your structure starts here.</text><text x="500" y="215" text-anchor="middle" class="svg-value">Choose Draw member. Click a start point and an end point.</text>`;
    svg.innerHTML = drawing;
    fitCanvasAnnotations();
}

/** Keep labels legible at the canvas edges without moving their force vectors.
 * Measure all labels before writing positions to avoid repeated layout passes.
 */
function fitCanvasAnnotations(): void {
    const bounds = svg.getBoundingClientRect();
    const pixelScale = svg.getScreenCTM()?.a;
    if (!pixelScale || bounds.width === 0) return;
    const adjustments = Array.from(svg.querySelectorAll<SVGTextElement>('.svg-label, .svg-value')).map(label => {
        const box = label.getBoundingClientRect();
        const shift = box.left < bounds.left + 8 ? bounds.left + 8 - box.left
            : box.right > bounds.right - 8 ? bounds.right - 8 - box.right : 0;
        return { label, x: Number(label.getAttribute('x')) + shift / pixelScale, shift };
    });
    for (const { label, x, shift } of adjustments) {
        if (shift) label.setAttribute('x', String(x));
    }
}
// Re-establish original label anchors after a viewport or font-metric change.
window.addEventListener('resize', renderCanvas);
void document.fonts.ready.then(renderCanvas);
function inspector(): void {
    renderInspector({
        container: $('inspector'), model, analysis, selected,
        resultsVisible: mode !== 'practice' || practiceResultsVisible,
        commit, clearSelection: () => { selected = null; inspector(); },
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
    return sampleSection(analysis, currentMember, sectionT);
}
function render() {
    if (!model.members.some(m => m.id === currentMember))
        currentMember = model.members[0]?.id || '';
    updateEvidenceBinding();
    renderResponses({ model, analysis, currentMember, sectionT, layer,
        resultsVisible: mode !== 'practice' || practiceResultsVisible });
    controls.setHistory(history.length > 0, future.length > 0);
    inspector();
    $('edit-selection').hidden = !selected;
    (document.querySelector('.right-panel') as HTMLElement).hidden = !selected;
    $('moment-options').hidden = layer !== 'M';
    renderCanvas();
    if (mode === 'practice')
        renderPractice();
    session.updateStatus();
    renderWorked({ model, section: sectionT, practice: mode === 'practice', connected: session.connected,
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
    const p = world(event), object = (event.target as Element).closest<SVGElement>('[data-object]');
    if (event.button === 1 || event.button === 2) {
        drag = { kind: 'pan', x: event.clientX, y: event.clientY, cx: view.cx, cy: view.cy };
        svg.setPointerCapture(event.pointerId);
        return;
    }
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
            toast('Choose both distributed-load boundaries on the same member.');
            return;
        }
        if (Math.abs(start.t! - attachment.t) < 1e-5) {
            toast('Choose a nonzero load interval.');
            return;
        }
        commit(() => model.loads.push({ id: id('q'), member: attachment.member, kind: 'distributed', t: Math.min(start!.t!, attachment.t), end: Math.max(start!.t!, attachment.t), fx: 0, fy: -5, mz: 0, qEnd: -5 }));
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
        }
        else {
            const load: Load = { id: id('L'), ...attachment, kind: tool as Load['kind'], end: 1, fx: 0, fy: -20, mz: 20, qEnd: -5 };
            model.loads.push(load);
            selected = { type: 'load', id: load.id };
        }
    });
});
svg.addEventListener('pointermove', event => {
    // Re-rendering the SVG can detach the original pointer target. A released
    // button must end a drag even when the browser omits the expected up event.
    if (drag && event.buttons === 0) {
        endDrag();
    }
    const p = world(event);
    $('coordinates').textContent = `x ${p.x.toFixed(2)} m · y ${p.y.toFixed(2)} m`;
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
                t = Math.min(t, 1 - width);
                load.end = t + width;
            }
            item.t = t;
        }
        analysis = analyse(model);
        render();
        return;
    }
    hover = snap(p);
    if (start || tool !== 'select')
        renderCanvas();
});
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
    controls.showMode(mode);
    $('page-title').textContent = mode === 'sandbox' ? 'Explore a structure' : mode === 'practice' ? 'Work through a problem' : 'Review learning progress';
    $('page-description').textContent = mode === 'sandbox' ? 'Draw a system. Change a load. Follow the response.' : mode === 'practice' ? 'Build the model, submit a step, and examine the reasoning.' : 'Review submitted steps and the evidence behind recurring errors.';
    $('practice-panel').hidden = mode !== 'practice';
    $('insights-panel').hidden = mode !== 'insights';
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
$('focus-workspace').onclick = () => controls.setFocus($('focus-workspace').getAttribute('aria-pressed') !== 'true');
$('close-inspector').onclick = () => { selected = null; render(); };
$('help-button').onclick = () => $<HTMLDialogElement>('workspace-help').showModal();
$('edit-selection').onclick = () => {
    controls.setFocus(false);
    document.querySelector('.inspector-panel')!.scrollIntoView({ behavior: 'smooth', block: 'start' });
};
$('undo').onclick = () => { if (!history.length)
    return; future.push(clone(model)); model = history.pop()!; selected = null; start = null; changed(); };
$('redo').onclick = () => { if (!future.length)
    return; history.push(clone(model)); model = future.pop()!; selected = null; changed(); };
document.addEventListener('keydown', event => { if ((event.target as HTMLElement).matches('input,select,textarea'))
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
$<HTMLInputElement>('section-position').oninput = () => { sectionT = Number($<HTMLInputElement>('section-position').value) / 1000; updateEvidenceBinding(); render(); };
$('export-model').onclick = () => download('cv2011-model.json', { version: 2, model });
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
$<HTMLInputElement>('model-file').onchange = async () => { try {
    const file = $<HTMLInputElement>('model-file').files?.[0];
    if (!file)
        return;
    if (file.size > 100000)
        throw Error('Model file is too large.');
    const source = await file.text();
    const parsed = JSON.parse(source), candidate = parsed.model || parsed;
    if (parsed.version && parsed.version > 2) throw Error('This model uses a newer file format. Update Structural Explorer before opening it.');
    const checked = analyse(candidate);
    if (checked.status === 'invalid')
        throw Error(checked.message);
    commit(() => { model = candidate; selected = null; fit(); });
    // Keep original text only while its parsed snapshot still matches the drawing.
    try {
        if (JSON.stringify(parseEvidenceModel(JSON.parse(source))) === JSON.stringify(parseEvidenceModel(model))) evidenceRawSource = source;
    } catch { /* The ordinary importer can accept models outside the strict snapshot schema. */ }
}
catch (error) {
    toast(`Could not open model: ${String(error)}`);
} };
// Guided derivations currently cover a single horizontal, prismatic beam with
// one pin and one vertical roller. The sandbox accepts a wider model class.
function problem() {
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
    deflection: { title: 'Vertical displacement v at the cut (upward +)', units: 'mm', hint: 'Integrate the moment equation EI v″ = M twice on each interval. Apply the displacement boundary conditions at both supports and continuity of displacement v and physical slope θ = v′ at each continuous section. If using downward-positive virtual-work displacement Δ, enter v = −Δ.' },
};
function renderPractice() {
    const p = problem(), panel = $('practice-panel');
    if (!p) {
        panel.innerHTML = '<div class="panel-label">GUIDED SOLUTIONS</div><h2>Choose a supported beam problem</h2><p>Verified step checks in this release cover one horizontal member drawn left to right, one pin, and one vertical roller. Supports may lie inside the beam. Point forces, couples, and linearly varying distributed loads are supported. Use the sandbox for rigid-jointed frames.</p>';
        return;
    }
    const step = stepDefinitions[solutionStep];
    panel.innerHTML = `<div class="panel-label">STEP-BY-STEP WORKSPACE</div><h2>From equilibrium to displacement</h2><p class="small">Submit a value or an arithmetic expression. Use +, −, *, /, parentheses, and ^. Numeric inputs are checked against the current model and cut. Upward reactions and displacements are positive.</p><div class="steps">${Object.entries(stepDefinitions).map(([key, value], index) => `<button data-step="${key}" class="${solutionStep === key ? 'active' : ''}">${index + 1}. ${value.title.split(' at ')[0]}</button>`).join('')}</div><h2>${step.title}</h2><p class="small">Current cut: x = ${number(p.section)} m from the member start. ${['normal', 'shear', 'moment'].includes(solutionStep) ? 'Use the right-hand limit at an interior point action.' : ''}</p><div class="answer-row"><input id="answer" aria-label="Your answer" placeholder="Enter a value or expression"><select id="answer-units" aria-label="Answer units">${['kN', 'N', 'kN m', 'N m', 'mm', 'm'].map(u => `<option ${u === step.units ? 'selected' : ''}>${u}</option>`).join('')}</select><button class="primary" id="check-answer">Check step</button></div><button id="hint">Show hint</button> <button id="reveal">Reveal derivation</button><div id="step-feedback" aria-live="polite"></div>`;
    panel.insertAdjacentHTML('beforeend', `<div class="dialog-buttons"><button id="show-computed">${practiceResultsVisible ? 'Hide computed response' : 'Reveal computed response'}</button></div><details class="small"><summary>Verification scope</summary><p>Symbolic checks run on the connected course verifier. Formal library: ${escape(proofStatus.lean === 'checked' ? 'Lean build passed' : 'Lean build status pending')}. ${escape(proofStatus.scope)} The drawing-to-model conversion and numerical solver are checked separately.</p></details>`);
    $('show-computed').onclick = () => { practiceResultsVisible = !practiceResultsVisible; if (practiceResultsVisible) {
        solutionRevealed = true;
        void record('reveal', '', step.units);
    } render(); };
    panel.querySelectorAll<HTMLButtonElement>('[data-step]').forEach(button => button.onclick = () => { solutionStep = button.dataset.step!; hintUsed = false; renderPractice(); });
    $('hint').onclick = () => { hintUsed = true; $('step-feedback').innerHTML = `<div class="feedback">${escape(step.hint)}</div>`; void record('hint', '', step.units); };
    $('reveal').onclick = async () => {
        solutionRevealed = true;
        const attempt = await record('reveal', '', step.units);
        if (attempt.step !== solutionStep || attempt.section !== sectionT || JSON.stringify(attempt.model) !== JSON.stringify(model) || mode !== 'practice') return;
        if (session.connected) {
            showWorkedSolution(solutionStep === 'deflection' ? 'integration' : 'sections');
        } else {
            const expected = expectedValue(p);
            $('step-feedback').innerHTML = `<div class="feedback">Numerical reference: ${number(expected, 5)} ${step.units}. Connect the verifier for a symbolic derivation.<p>${escape(step.hint)}</p></div>`;
        }
    };
    $('check-answer').onclick = async () => {
        const answer = $<HTMLInputElement>('answer').value.trim(), units = $<HTMLSelectElement>('answer-units').value;
        if (!answer) {
            toast('Enter an answer first.');
            return;
        }
        $<HTMLButtonElement>('check-answer').disabled = true;
        const attempt = await record('submit', answer, units);
        if (attempt.step !== solutionStep || attempt.section !== sectionT || JSON.stringify(attempt.model) !== JSON.stringify(model) || mode !== 'practice') {
            toast('The result was recorded for the model and step you submitted.');
            return;
        }
        const result = attempt.result!;
        $('step-feedback').innerHTML = `<div class="feedback ${result.status === 'incorrect' ? 'incorrect' : ''}"><b>${escape(result.status === 'correct' ? 'Correct' : result.status === 'incorrect' ? 'Check this step' : 'Awaiting verification')}</b><p>${escape(result.message)}</p><span class="small">${attempt.synced ? 'Recorded by the verifier.' : 'Saved on this device; not yet verified by the server.'}</span></div>`;
        $<HTMLButtonElement>('check-answer').disabled = false;
    };
    $<HTMLInputElement>('answer').onkeydown = event => { if (event.key === 'Enter')
        $('check-answer').click(); };
}
function expectedValue(p: NonNullable<ReturnType<typeof problem>>) { return { reaction_left: p.left.fy, reaction_right: p.right.fy, normal: p.N, shear: p.V, moment: p.M, deflection: p.deflection }[solutionStep]!; }
function record(event: string, answer: string, units: string): Promise<Attempt> {
    return session.record({ model, section: sectionT, step: solutionStep, side, hintUsed,
        solutionRevealed: solutionRevealed || practiceResultsVisible }, event, answer, units);
}
// Components bind once. Model edits and navigation still share this controller.
const controls = createWorkspaceControls({
    selectTool: next => { tool = next; start = null; renderCanvas(); },
    selectLayer: next => { layer = next; render(); },
    selectMode: setMode,
});
const session = createLearningSession({ notify: toast, onConnectionChange: render });
portalPanel = createPortalPanel(() => model, value => commit(() => {
    if (model.loads.length === 1) { model.loads[0].fy = value; model.loads[0].qEnd = value; }
}));
fit();
setMode(location.hash.slice(1) || 'sandbox');
void session.connect();
void fetch('verification.json').then(r => r.json()).then(v => { proofStatus = v; }).catch(() => { });
