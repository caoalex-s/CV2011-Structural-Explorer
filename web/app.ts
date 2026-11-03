import { analyse, example, position, splitMember, nodeLabels, endConnection, referenceMember } from './engine.js';
import type { Model, Analysis, Point, Member, Support, Load, Sample, Connection, ConnectionRule } from './engine.js';
import { courseColors, forceSymbol, momentSymbol, rotationalSpring, supportShape } from './symbols.js';
import { renderWorked, showWorkedSolution } from './worked.js';
import { renderCourseConventions } from './course.js';
import { math } from './math.js';
const $ = <T extends HTMLElement = HTMLElement>(id: string) => document.getElementById(id) as T;
const escape = (value: unknown) => String(value).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]!));
const number = (value: number, digits = 3) => Math.abs(value) < 1e-8 ? '0' : Number(value.toPrecision(digits)).toString();
const clone = <T>(value: T): T => structuredClone(value);
const id = (prefix: string) => `${prefix}${crypto.randomUUID().slice(0, 6)}`;
renderCourseConventions();
let model: Model = example();
try {
    const saved = localStorage.getItem('cv2011-model');
    if (saved) {
        const candidate = JSON.parse(saved);
        if (analyse(candidate).status !== 'invalid')
            model = candidate;
    }
}
catch { /* Recover from stale browser storage with the default model. */ }
let analysis: Analysis = analyse(model);
let tool = 'select', layer = 'M', mode = 'sandbox', side = 'tension';
let selected: {
    type: string;
    id: string;
} | null = null;
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
let currentMember = model.members[0]?.id || '', sectionT = 0.5;
let solutionStep = 'reaction_left', solutionRevealed = false, hintUsed = false, practiceResultsVisible = false;
let proofStatus = { lean: 'pending', scope: 'Scaled reaction equilibrium identities and plotting-side inversion.' };
let online = false, localDemo = false;
let config = { url: localStorage.getItem('cv2011-api') || (['localhost', '127.0.0.1'].includes(location.hostname) ? location.origin : ''), courseId: localStorage.getItem('cv2011-id') || '', token: sessionStorage.getItem('cv2011-token') || '', instructor: sessionStorage.getItem('cv2011-instructor') || '' };
const svg = $('canvas') as unknown as SVGSVGElement;
interface Snap {
    x: number;
    y: number;
    node?: string;
    member?: string;
    t?: number;
}
interface Attempt {
    id: string;
    timestamp: string;
    courseId: string;
    event: string;
    model: Model;
    section: number;
    step: string;
    answer: string;
    units: string;
    side: string;
    hintUsed: boolean;
    solutionRevealed: boolean;
    result?: {
        status: string;
        category: string;
        message: string;
    };
    synced?: boolean;
}
let attempts: Attempt[] = [];
try {
    attempts = JSON.parse(localStorage.getItem('cv2011-attempts') || '[]');
}
catch {
    attempts = [];
}
function toast(message: string) { $('toast').textContent = message; $('toast').classList.add('show'); setTimeout(() => $('toast').classList.remove('show'), 4200); }
function saveAttempts() { localStorage.setItem('cv2011-attempts', JSON.stringify(attempts)); updateSession(); }
function checkpoint(before = model) { history.push(clone(before)); if (history.length > 60)
    history.shift(); future.length = 0; }
function changed() { analysis = analyse(model); localStorage.setItem('cv2011-model', JSON.stringify(model)); render(); }
function commit(action: () => void) { checkpoint(); action(); solutionRevealed = false; hintUsed = false; practiceResultsVisible = false; changed(); }
function screen(point: {
    x: number;
    y: number;
}) { return { x: 500 + (point.x - view.cx) * view.scale, y: 260 - (point.y - view.cy) * view.scale }; }
function world(event: PointerEvent | WheelEvent) { const p = new DOMPoint(event.clientX, event.clientY).matrixTransform(svg.getScreenCTM()!.inverse()); return { x: view.cx + (p.x - 500) / view.scale, y: view.cy - (p.y - 260) / view.scale }; }
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
    view = { cx: (minX + maxX) / 2, cy: (minY + maxY) / 2, scale: Math.min(100, 760 / Math.max(maxX - minX, 1), 280 / Math.max(maxY - minY, 1)) };
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
    const color = courseColors.force;
    const tag = `class="clickable" data-object="load" data-id="${escape(load.id)}"`;
    if (load.kind === 'force' && Math.hypot(load.fx, load.fy) < 1e-12 || load.kind === 'moment' && Math.abs(load.mz) < 1e-12)
        return `<g ${tag}><circle cx="${p.x}" cy="${p.y}" r="16" class="node-hit"/><text x="${p.x + 8}" y="${p.y - 15}" class="svg-label">0 ${load.kind === 'force' ? 'kN' : 'kN m'}</text></g>`;
    if (load.kind === 'force') {
        const magnitude = Math.hypot(load.fx, load.fy);
        return `<g ${tag}>${forceSymbol(p.x, p.y, load.fx, load.fy, color, `${number(magnitude)} kN`)}</g>`;
    }
    if (load.kind === 'moment') {
        return `<g ${tag}>${momentSymbol(p.x, p.y, load.mz, color, `${number(Math.abs(load.mz))} kN m`)}</g>`;
    }
    const end = screen(position(model, load.member, load.end));
    const max = Math.max(Math.abs(load.fy), Math.abs(load.qEnd), 1);
    let result = `<g ${tag}><path class="hit" d="M ${p.x} ${p.y + load.fy / max * 53} L ${end.x} ${end.y + load.qEnd / max * 53}"/>`;
    const count = Math.max(3, Math.ceil(Math.hypot(end.x - p.x, end.y - p.y) / 27));
    for (let i = 0; i <= count; i++) {
        const t = i / count, q = load.fy + (load.qEnd - load.fy) * t;
        result += drawArrow(p.x + (end.x - p.x) * t, p.y + (end.y - p.y) * t, 0, -q / max * 53, color);
    }
    result += `<path d="M ${p.x} ${p.y + load.fy / max * 53} L ${end.x} ${end.y + load.qEnd / max * 53}" stroke="${color}" fill="none"/><text class="svg-label" x="${(p.x + end.x) / 2}" y="${Math.min(p.y, end.y) - 67}" text-anchor="middle">w = ${number(-load.fy)}${load.qEnd !== load.fy ? ' → ' + number(-load.qEnd) : ''} kN/m (↓ +)</text></g>`;
    return result;
}
function memberLabel(member: Member): string {
    const labels = nodeLabels(model);
    return `${labels.get(member.a)}–${labels.get(member.b)}`;
}
function jointConnections(node: Point) {
    return model.members.filter(member => member.a === node.id || member.b === node.id).map(member => {
        const end = member.a === node.id ? 'a' : 'b';
        return { member, end: end as 'a' | 'b', rule: endConnection(model, member, end) };
    });
}
function jointDrawing(node: Point) {
    const p = screen(node), connected = jointConnections(node);
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
    const grid = Math.max(0.05, Number($<HTMLInputElement>('grid-spacing').value) || 0.5);
    const spacing = grid * view.scale;
    const origin = screen({ x: 0, y: 0 });
    let drawing = `<defs><pattern id="grid" width="${spacing}" height="${spacing}" patternUnits="userSpaceOnUse" x="${origin.x % spacing}" y="${origin.y % spacing}"><circle cx="0" cy="0" r="1" fill="#dce5df"/></pattern></defs><rect width="1000" height="520" fill="url(#grid)"/><text x="22" y="29" class="svg-value">${escape(mode === 'practice' ? 'PROBLEM WORKSPACE' : 'EXPLORATION WORKSPACE')}</text>`;
    const all = analysis.elements.flatMap(e => e.samples);
    if (analysis.status === 'stable' && layer !== 'none' && (mode !== 'practice' || practiceResultsVisible)) {
        if (layer === 'displacement') {
            const maximum = Math.max(...all.map(p => Math.hypot(p.ux, p.uy)), 1e-12), magnification = 55 / (view.scale * maximum);
            for (const element of analysis.elements) {
                const path = element.samples.map((p, i) => { const q = screen({ x: p.x + p.ux * magnification, y: p.y + p.uy * magnification }); return `${i ? 'L' : 'M'} ${q.x} ${q.y}`; }).join(' ');
                drawing += `<path d="${path}" fill="none" stroke="${courseColors.reaction}" stroke-width="2.5"/>`;
            }
            drawing += `<text x="22" y="495" class="svg-value">Displacement magnification ×${number(magnification)} · values are unscaled</text>`;
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
                drawing += `<text x="22" y="495" class="svg-value">Peak |${field}| = ${number(Math.abs(peak[field]))} ${field === 'M' ? 'kN m' : 'kN'} · diagrams scaled to fit</text>`;
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
                drawing += `<g pointer-events="none">${forceSymbol(p.x, p.y, 0, reaction.fy, courseColors.reaction, `${label}ᵧ = ${number(Math.abs(reaction.fy))} kN`, 42, 44)}</g>`;
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
        drawing += `<text x="500" y="235" text-anchor="middle" class="svg-label" style="font-size:23px">Your structure starts here.</text><text x="500" y="265" text-anchor="middle" class="svg-value">Choose Draw member. Click a start point and an end point.</text>`;
    svg.innerHTML = drawing;
}
function connectionEditor(member: Member, end: 'a' | 'b'): string {
    const node = model.nodes.find(node => node.id === member[end])!;
    const label = `${memberLabel(member)} at ${nodeLabels(model).get(node.id)}`;
    if (referenceMember(model, node.id) === member.id) return `<p class="small"><b>${label}</b>: reference side</p>`;
    const connection = endConnection(model, member, end);
    const rows = (['axial', 'transverse', 'rotation'] as const).map(direction => {
        const value = connection[direction], name = direction === 'axial' ? 'Axial N / local x' : direction === 'transverse' ? 'Shear V / local y' : 'Moment M / rotation';
        const attributes = `data-connection-member="${escape(member.id)}" data-end="${end}" data-direction="${direction}"`;
        return `<label class="field">${name}<select ${attributes} aria-label="${name}: ${label}">${[['rigid', 'Continuous'], ['free', 'Released'], ['spring', 'Elastic spring']].map(([key, caption]) => `<option value="${key}" ${key === (typeof value === 'number' ? 'spring' : value) ? 'selected' : ''}>${caption}</option>`).join('')}</select></label>${typeof value === 'number' ? `<label class="field">Stiffness (${direction === 'rotation' ? 'kN m/rad' : 'kN/m'})<input type="number" min="0" step="any" value="${value}" ${attributes} data-stiffness="true" aria-label="${direction} stiffness: ${label}"></label>` : ''}`;
    }).join('');
    const result = analysis.connections?.find(item => item.member === member.id && item.end === end);
    const response = result && (mode !== 'practice' || practiceResultsVisible) ? `<p class="small">Relative rotation Δθ = ${number(result.relativeRotation)} rad<br>Axial slip = ${number(result.axialSlip * 1000)} mm<br>Transverse slip = ${number(result.transverseSlip * 1000)} mm</p>` : '';
    return `<details class="connection-editor" open><summary>${label}</summary>${rows}${response}</details>`;
}
function bindConnectionEditors(container: HTMLElement) {
    container.querySelectorAll<HTMLInputElement | HTMLSelectElement>('[data-connection-member]').forEach(input => input.onchange = () => {
        const member = model.members.find(member => member.id === input.dataset.connectionMember)!;
        const end = input.dataset.end as 'a' | 'b', direction = input.dataset.direction as keyof Connection;
        const node = model.nodes.find(node => node.id === member[end])!;
        let value: ConnectionRule = input.value === 'spring' ? (direction === 'rotation' ? 20000 : 100000) : input.value as ConnectionRule;
        if (input.dataset.stiffness) {
            value = Number(input.value);
            if (!Number.isFinite(value) || value <= 0) { toast('Use a positive spring stiffness, or choose Released.'); inspector(); return; }
        }
        commit(() => {
            // Preserve every other end when converting a preset to a mixed joint.
            for (const item of jointConnections(node)) {
                if (item.member.id === referenceMember(model, node.id)) continue;
                if (item.end === 'a') item.member.connectionA = { ...item.rule }; else item.member.connectionB = { ...item.rule };
            }
            node.joint = 'custom';
            const rule = { ...endConnection(model, member, end), [direction]: value };
            if (end === 'a') member.connectionA = rule; else member.connectionB = rule;
        });
    });
}
function inspector() {
    const container = $('inspector');
    if (!selected) {
        container.innerHTML = '<p class="small">Select an object to edit its position, loading, or stiffness.</p>';
        return;
    }
    const collection = selected.type === 'node' ? model.nodes : selected.type === 'member' ? model.members : selected.type === 'support' ? model.supports : model.loads;
    const item = collection.find(i => i.id === selected!.id) as unknown as Record<string, string | number>;
    if (!item) {
        selected = null;
        inspector();
        return;
    }
    // Load intensity is presented downward-positive as in Tutorial 5. Stored
    // force components remain upward-positive for model-file compatibility.
    const field = (key: string, label: string, step = 'any', direction = 1) => `<label class="field">${label}<input type="number" data-property="${key}" data-direction="${direction}" value="${Number(item[key] ?? (key === 'rotationStiffness' ? 20000 : 0)) * direction}" step="${step}"></label>`;
    let html = `<h3>${escape(selected.type[0].toUpperCase() + selected.type.slice(1))} properties</h3>`;
    if (selected.type === 'load' || selected.type === 'support') html += `<label class="field">Attached member<select data-property="member">${model.members.map(member => `<option value="${escape(member.id)}" ${member.id === item.member ? 'selected' : ''}>${memberLabel(member)}</option>`).join('')}</select></label>`;
    if (selected.type === 'node') {
        const node = model.nodes.find(node => node.id === selected!.id)!;
        const connected = jointConnections(node), reference = referenceMember(model, node.id);
        html += `<p class="small">Node <b>${nodeLabels(model).get(node.id)}</b> · labels update automatically when nodes are added or removed.</p>` + field('x', 'x (m)') + field('y', 'y (m)');
        const jointNames: Record<string, string> = { rigid: 'Rigid joint', pinned: 'Internal pin / hinge', 'semi-rigid': 'Semi-rigid joint', custom: 'Member-specific constraints' };
        html += `<label class="field">Joint connection<select data-property="joint">${Object.entries(jointNames).map(([kind, label]) => `<option value="${kind}" ${kind === (node.joint || 'rigid') ? 'selected' : ''}>${label}</option>`).join('')}</select></label>`;
        if (node.joint === 'semi-rigid') html += field('rotationStiffness', 'Rotational stiffness kθ (kN m/rad)');
        if (connected.length > 1) html += `<label class="field">Reference member<select data-property="referenceMember">${connected.map(({ member }) => `<option value="${escape(member.id)}" ${member.id === reference ? 'selected' : ''}>${memberLabel(member)}</option>`).join('')}</select></label><p class="small">Connections relate each other member end to this reference. A pin shares translations and permits relative rotation. A rotational spring transfers moment M = kθ Δθ.</p>${connected.map(({ member, end }) => connectionEditor(member, end)).join('')}`;
        else html += '<p class="small">A joint connection relates two or more members. At a single-member end, use a ground support to constrain movement.</p>';
    }
    if (selected.type === 'member') {
        const member = model.members.find(member => member.id === selected!.id)!;
        html += `<p class="small">Member <b>${memberLabel(member)}</b></p>` + field('EA', 'Axial rigidity EA (kN)') + field('EI', 'Flexural rigidity EI (kN m²)');
        html += connectionEditor(member, 'a') + connectionEditor(member, 'b');
    }
    if (selected.type === 'support')
        html += `<label class="field">Support type<select data-property="kind">${['pin', 'roller', 'fixed', 'guided', 'custom'].map(k => `<option ${item.kind === k ? 'selected' : ''}>${k}</option>`).join('')}</select></label>` + field('t', 'Position / member length', '0.01') + (['roller', 'guided'].includes(String(item.kind)) ? field('angle', 'Restrained translation angle from +x (°)') : '') + (item.kind === 'custom' ? [['fixX', 'Restrain global x'], ['fixY', 'Restrain global y'], ['fixRotation', 'Restrain rotation θ']].map(([key, label]) => `<label class="check"><input type="checkbox" data-property="${key}" ${item[key] ? 'checked' : ''}>${label}</label>`).join('') : '') + '<p class="small">Ground restraints act on the selected member side. A pin support does not release continuity between connected members.</p>';
    if (selected.type === 'load') {
        html += '<p class="small">The action belongs to this member side at a joint. Arrows retain their physical line of action; moment arcs retain their application centre.</p>';
        html += field('t', 'Start / member length', '0.01');
        if (item.kind === 'force')
            html += field('fx', 'Horizontal force Fx, rightward + (kN)') + field('fy', 'Vertical force Fy, upward + (kN)');
        if (item.kind === 'moment')
            html += field('mz', 'Moment, CCW + (kN m)');
        if (item.kind === 'distributed')
            html += field('end', 'End / member length', '0.01') + field('fy', 'Start intensity w, downward + (kN/m)', 'any', -1) + field('qEnd', 'End intensity w, downward + (kN/m)', 'any', -1);
    }
    container.innerHTML = html + '<button id="delete-selected">Delete selected object</button>';
    container.querySelectorAll<HTMLInputElement | HTMLSelectElement>('[data-property]').forEach(input => input.addEventListener('change', () => {
        const key = input.dataset.property!;
        const value = input.type === 'checkbox' ? (input as HTMLInputElement).checked : ['kind', 'joint', 'referenceMember', 'member'].includes(key) ? input.value : Number(input.value) * Number(input.dataset.direction || 1);
        if (typeof value === 'number' && !Number.isFinite(value)) {
            toast('Enter a finite number.');
            return;
        }
        if ((key === 't' || key === 'end') && (Number(value) < 0 || Number(value) > 1)) {
            toast('Member positions range from 0 to 1.');
            inspector();
            return;
        }
        commit(() => {
            const previousConnections = selected?.type === 'node' && key === 'joint' ? jointConnections(model.nodes.find(node => node.id === selected!.id)!) : [];
            if (key === 'member') {
                const point = position(model, String(item.member), Number(item.t));
                const next = model.members.find(member => member.id === value)!;
                const projected = projection(point, next);
                item.t = projected.t;
            }
            (item as Record<string, unknown>)[key] = value;
            if (selected?.type === 'node' && key === 'joint') {
                const node = model.nodes.find(node => node.id === selected!.id)!;
                if (value === 'semi-rigid' && !node.rotationStiffness) node.rotationStiffness = 20000;
                // Physical presets replace the connections. Entering the custom
                // editor retains the existing behaviour until a direction changes.
                for (const { member, end, rule } of previousConnections) {
                    if (value === 'custom') {
                        if (end === 'a') member.connectionA = { ...rule }; else member.connectionB = { ...rule };
                    } else if (end === 'a') delete member.connectionA; else delete member.connectionB;
                }
            }
        });
    }));
    bindConnectionEditors(container);
    $('delete-selected').onclick = () => removeSelected();
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
    const elements = analysis.elements.filter(e => e.member === currentMember);
    // At a point action use the right-hand section, except at the member end.
    const element = elements.find(e => sectionT >= e.t0 - 1e-9 && sectionT < e.t1 - 1e-9) || elements.at(-1);
    if (!element)
        return;
    const u = Math.max(0, Math.min(40, (sectionT - element.t0) / (element.t1 - element.t0) * 40));
    const left = element.samples[Math.floor(u)], right = element.samples[Math.min(40, Math.ceil(u))], fraction = u - Math.floor(u);
    const sample = { ...left };
    for (const key of ['N', 'V', 'M', 'ux', 'uy', 'rotation'] as const)
        sample[key] = left[key] + fraction * (right[key] - left[key]);
    return sample;
}
function render() {
    if (!model.members.some(m => m.id === currentMember))
        currentMember = model.members[0]?.id || '';
    $<HTMLSelectElement>('section-member').innerHTML = model.members.map(m => `<option value="${escape(m.id)}" ${m.id === currentMember ? 'selected' : ''}>${memberLabel(m)}</option>`).join('');
    const member = model.members.find(m => m.id === currentMember);
    const length = member ? Math.hypot(position(model, member.id, 1).x - position(model, member.id, 0).x, position(model, member.id, 1).y - position(model, member.id, 0).y) : 0;
    $('section-distance').textContent = `x = ${number(sectionT * length)} / ${number(length)} m`;
    const sample = sectionSample();
    $('section-results').innerHTML = [['Normal force N', sample?.N, 'kN'], ['Shear force V', sample?.V, 'kN'], ['Bending moment M', sample?.M, 'kN m'], ['Vertical displacement v (upward +)', sample ? sample.uy * 1000 : undefined, 'mm']].map(([label, value, unit]) => `<div class="metric"><small>${label}</small><strong>${value === undefined ? '—' : number(Number(value), 4)} <em>${unit}</em></strong></div>`).join('');
    $('status').innerHTML = `<span class="status-pill ${analysis.status}">${analysis.status === 'stable' ? '● Stable' : analysis.status === 'unstable' ? '○ Unstable (mechanism)' : analysis.status === 'empty' ? 'Start drawing' : 'Check model'}</span><p class="small">${escape(analysis.message)}</p>${analysis.status === 'stable' ? `<p class="small">Degree of static indeterminacy: ${analysis.degree}.<br>No free motion in the small-displacement model.</p><details class="small"><summary>Numerical check</summary>Restrained stiffness matrix has full rank.<br>Equilibrium residual: ${analysis.residual!.toExponential(1)}</details>` : ''}`;
    $('reactions').innerHTML = analysis.reactions.map((r, i) => {
        const node = model.nodes.find(node => Math.hypot(node.x - r.x, node.y - r.y) < 1e-7);
        const name = node ? `Node ${nodeLabels(model).get(node.id)}` : `Support ${i + 1}`;
        const label = node ? nodeLabels(model).get(node.id)! : 'R';
        const component = (direction: string) => `${label}_{${node ? '' : i + 1}${direction}}`;
        return `<div class="reaction-row"><b>${name} · (${number(r.x)}, ${number(r.y)}) m</b><span>${math(component('x'))}: ${number(r.fx)} · ${math(component('y'))}: ${number(r.fy)} kN</span>${Math.abs(r.mz) > 1e-7 ? `<span>${math(`M_{${node ? label : `R${i+1}`}}`)}: ${number(r.mz)} kN m (CCW +)</span>` : ''}</div>`;
    }).join('');
    $('reactions').hidden = mode === 'practice' && !practiceResultsVisible;
    $('section-results').hidden = mode === 'practice' && !practiceResultsVisible;
    const descriptions: Record<string, [
        string,
        string
    ]> = { M: ['Bending moment', 'For a horizontal member directed rightward, positive M is sagging with tension at the bottom. The Week 4 lecture plots on the tension side; worked tutorials plot on the compression side. Changing the plotting side preserves the signed moment. For an inclined member, use its local axis from the first joint to the second.'], V: ['Shear force', 'Positive V acts downward on the right cut face of the retained left portion. On the opposite cut face its arrow reverses. Between concentrated actions, dM/dx = V and dV/dx = −w for downward-positive distributed intensity w.'], N: ['Normal force', 'Positive normal force N represents tension. Negative values represent compression. The local member axis runs from the first joint to the second.'], displacement: ['Deflected shape and elastic curve', 'The elastic curve gives signed displacement, with vertical v positive upward. Physical slope θ = dv/dx is counterclockwise-positive for rightward x and small rotations. The drawing magnifies displacement; numerical values retain their actual magnitude. The frame solver includes bending and axial deformation.'], none: ['Structural model', 'Click a joint, support, load, or member to inspect it. Snap to a member interior while drawing to create a rigid connection. Crossing members remain separate.'] };
    $('response-title').textContent = descriptions[layer][0];
    $('response-description').textContent = descriptions[layer][1];
    $('legend').innerHTML = `<div class="legend-item"><span class="swatch" style="background:${courseColors.force}"></span>Applied forces and moments</div><div class="legend-item"><span class="swatch" style="background:${courseColors.reaction}"></span>Reactions and displaced shape</div><p class="small">● Rigid continuity · ○ Pin / hinge<br>Spiral: rotational spring<br>Circle between rails: sliding joint<br>◇ Member-specific constraints</p><p class="small">Forces stay on their lines of action. Moment arcs are centred at their application points. A ground pin does not create an internal hinge.</p><p class="small">At a point action the section readout uses the right-hand limit, except at the member end. Values between plotted samples are interpolated.</p>`;
    $<HTMLButtonElement>('undo').disabled = !history.length;
    $<HTMLButtonElement>('redo').disabled = !future.length;
    inspector();
    renderCanvas();
    if (mode === 'practice')
        renderPractice();
    updateSession();
    renderWorked({ model, section: sectionT, practice: mode === 'practice', connected: online,
        request: payload => api('/api/worked-solution', payload),
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
document.querySelectorAll<HTMLButtonElement>('[data-tool]').forEach(button => button.onclick = () => {
    tool = button.dataset.tool!;
    start = null;
    document.querySelectorAll('[data-tool]').forEach(b => b.classList.toggle('active', (b as HTMLElement).dataset.tool === tool));
    const hints: Record<string, string> = { select: 'Select an object to edit it. Drag joints, loads, or supports.', member: 'Click the start and end points. Snap to a member to create a rigid joint.', distributed: 'Click the start and end of the loaded interval on one member.', delete: 'Click an object to delete it. Undo restores the previous model.' };
    $('tool-hint').textContent = hints[tool] || 'Click a member to place this object. Select it to edit its properties.';
    renderCanvas();
});
document.querySelectorAll<HTMLButtonElement>('[data-layer]').forEach(button => button.onclick = () => { layer = button.dataset.layer!; document.querySelectorAll('[data-layer]').forEach(b => b.classList.toggle('active', (b as HTMLElement).dataset.layer === layer)); render(); });
function setMode(next: string) { mode = ['sandbox', 'practice', 'insights'].includes(next) ? next : 'sandbox'; location.hash = mode; document.querySelectorAll('[data-mode]').forEach(b => b.classList.toggle('active', (b as HTMLElement).dataset.mode === mode)); $('page-title').textContent = mode === 'sandbox' ? 'Draw. Change. Understand.' : mode === 'practice' ? 'Work through the mechanics.' : 'Learn from the attempts.'; $('page-description').textContent = mode === 'sandbox' ? 'Move a load or change a restraint. Follow the response as it changes.' : mode === 'practice' ? 'Build the model, submit a step, and examine the reasoning.' : 'Review submitted steps and the evidence behind recurring errors.'; $('practice-panel').hidden = mode !== 'practice'; $('insights-panel').hidden = mode !== 'insights'; (document.querySelector('.work-grid') as HTMLElement).hidden = mode === 'insights'; (document.querySelector('.modelbar') as HTMLElement).hidden = mode === 'insights'; if (mode === 'insights')
    void renderInsights();
else
    render(); }
document.querySelectorAll<HTMLButtonElement>('[data-mode]').forEach(button => button.onclick = () => setMode(button.dataset.mode!));
window.addEventListener('hashchange', () => { if (location.hash.slice(1) !== mode)
    setMode(location.hash.slice(1)); });
$<HTMLSelectElement>('moment-side').onchange = () => { side = $<HTMLSelectElement>('moment-side').value; renderCanvas(); };
$<HTMLInputElement>('show-reactions').onchange = renderCanvas;
$<HTMLInputElement>('grid-spacing').onchange = renderCanvas;
$('zoom-in').onclick = () => { view.scale = Math.min(500, view.scale * 1.25); renderCanvas(); };
$('zoom-out').onclick = () => { view.scale = Math.max(10, view.scale / 1.25); renderCanvas(); };
$('fit').onclick = () => { fit(); renderCanvas(); };
$('undo').onclick = () => { if (!history.length)
    return; future.push(clone(model)); model = history.pop()!; selected = null; start = null; changed(); };
$('redo').onclick = () => { if (!future.length)
    return; history.push(clone(model)); model = future.pop()!; selected = null; changed(); };
document.addEventListener('keydown', event => { if ((event.target as HTMLElement).matches('input,select,textarea'))
    return; if (event.key === 'Escape') {
    start = null;
    drag = null;
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
$<HTMLSelectElement>('section-member').onchange = () => { currentMember = $<HTMLSelectElement>('section-member').value; render(); };
$<HTMLInputElement>('section-position').oninput = () => { sectionT = Number($<HTMLInputElement>('section-position').value) / 1000; render(); };
function download(name: string, data: unknown) { const url = URL.createObjectURL(new Blob([JSON.stringify(data, null, 2)], { type: 'application/json' })); const anchor = document.createElement('a'); anchor.href = url; anchor.download = name; anchor.click(); setTimeout(() => URL.revokeObjectURL(url), 1000); }
$('export-model').onclick = () => download('cv2011-model.json', { version: 2, model });
$('import-model').onclick = () => $('model-file').click();
$<HTMLInputElement>('model-file').onchange = async () => { try {
    const file = $<HTMLInputElement>('model-file').files?.[0];
    if (!file)
        return;
    if (file.size > 100000)
        throw Error('Model file is too large.');
    const parsed = JSON.parse(await file.text()), candidate = parsed.model || parsed;
    if (parsed.version && parsed.version > 2) throw Error('This model uses a newer file format. Update Structural Explorer before opening it.');
    const checked = analyse(candidate);
    if (checked.status === 'invalid')
        throw Error(checked.message);
    commit(() => { model = candidate; selected = null; fit(); });
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
        if (online) {
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
async function api(path: string, payload?: unknown, instructor = false): Promise<any> {
    if (!config.url)
        throw Error('No verifier configured.');
    const response = await fetch(config.url.replace(/\/$/, '') + path, { method: payload === undefined ? 'GET' : 'POST', headers: { 'Content-Type': 'application/json', 'Authorization': `Bearer ${instructor ? config.instructor : config.token}` }, body: payload === undefined ? undefined : JSON.stringify(payload), signal: AbortSignal.timeout(path === '/api/worked-solution' ? 60000 : 15000) });
    const result = await response.json();
    if (!response.ok)
        throw Error(result.error || 'Request failed');
    return result;
}
async function record(event: string, answer: string, units: string): Promise<Attempt> {
    const attempt: Attempt = { id: crypto.randomUUID(), timestamp: new Date().toISOString(), courseId: config.courseId || 'local-unassigned', event, model: clone(model), section: sectionT, step: solutionStep, answer, units, side, hintUsed, solutionRevealed: solutionRevealed || practiceResultsVisible };
    attempt.result = { status: 'unresolved', category: 'pending_verification', message: 'This submission will be checked after you connect to the verifier. You can export your local records.' };
    if (online)
        try {
            const response = await api('/api/attempts', attempt);
            attempt.result = response.result;
            attempt.synced = true;
        }
        catch (error) {
            toast(`Record retained locally: ${String(error)}`);
        }
    attempts.push(attempt);
    saveAttempts();
    return attempt;
}
function updateSession() {
    $('session-status').textContent = online ? `${localDemo ? 'Local verification service' : 'Connected verifier'} · ${config.courseId}. ${attempts.filter(a => a.synced).length} recorded events on this device.` : `Local exploration · ${attempts.filter(a => !a.synced).length} events awaiting verification. Connect your course verifier to record class results.`;
}
async function connect() {
    online = false;
    localDemo = false;
    if (config.url)
        try {
            const response = await fetch(config.url.replace(/\/$/, '') + '/api/health', { signal: AbortSignal.timeout(3000) });
            const health = await response.json();
            if (health.localDemo && !config.token) {
                config.courseId = health.localDemo.courseId;
                config.token = health.localDemo.token;
                config.instructor = health.localDemo.instructor;
                sessionStorage.setItem('cv2011-token', config.token);
                sessionStorage.setItem('cv2011-instructor', config.instructor);
            }
            localDemo = !!health.localDemo;
            online = health.sympy === true && !!config.token;
            if (online) {
                const identity = await api('/api/me');
                if (identity.courseId !== config.courseId && config.courseId)
                    throw Error('Course ID does not correspond to this access token.');
                config.courseId = identity.courseId;
            }
        }
        catch {
            online = false;
        }
    render();
}
$('settings-button').onclick = () => { $<HTMLInputElement>('api-url').value = config.url; $<HTMLInputElement>('course-id').value = config.courseId; $<HTMLInputElement>('access-token').value = config.token; $<HTMLInputElement>('instructor-token').value = config.instructor; $<HTMLDialogElement>('settings').showModal(); };
$('save-settings').onclick = async () => { config = { url: $<HTMLInputElement>('api-url').value.trim(), courseId: $<HTMLInputElement>('course-id').value.trim(), token: $<HTMLInputElement>('access-token').value.trim(), instructor: $<HTMLInputElement>('instructor-token').value.trim() }; localStorage.setItem('cv2011-api', config.url); localStorage.setItem('cv2011-id', config.courseId); sessionStorage.setItem('cv2011-token', config.token); sessionStorage.setItem('cv2011-instructor', config.instructor); await connect(); toast(online ? 'Connected to the verifier.' : 'Connection unavailable. Records remain on this device.'); };
async function renderInsights() {
    const panel = $('insights-panel');
    let records: Attempt[] = attempts, scope = 'Records from this browser';
    if (online && config.instructor)
        try {
            const response = await api('/api/instructor/attempts', undefined, true);
            records = response.attempts;
            scope = 'Instructor view · all records from the connected course service';
        }
        catch (error) {
            toast(String(error));
        }
    const submissions = records.filter(a => a.event === 'submit'), checked = submissions.filter(a => ['correct', 'incorrect'].includes(a.result?.status || ''));
    const wrong = checked.filter(a => a.result?.status === 'incorrect'), categories: Record<string, number> = {};
    wrong.forEach(a => { const category = a.result?.category || 'unclassified'; categories[category] = (categories[category] || 0) + 1; });
    panel.innerHTML = `<div class="panel-label">LEARNING INSIGHTS</div><h2>${escape(scope)}</h2><p>Counts describe submitted problem steps. Exploration edits are excluded. An error category describes the observed answer pattern and can require instructor interpretation.</p><div class="insights-cards"><div class="panel"><div class="insight-number">${submissions.length}</div><p>Submitted steps</p></div><div class="panel"><div class="insight-number">${checked.length ? Math.round(100 * (checked.length - wrong.length) / checked.length) + '%' : '—'}</div><p>Correct among verified submissions</p></div><div class="panel"><div class="insight-number">${new Set(records.map(a => a.courseId)).size}</div><p>Pseudonymous IDs</p></div></div><h2>Observed answer patterns</h2>${Object.keys(categories).length ? `<table class="data-table"><thead><tr><th>Pattern</th><th>Occurrences</th></tr></thead><tbody>${Object.entries(categories).map(([name, count]) => `<tr><td>${escape(name.replaceAll('_', ' '))}</td><td>${count}</td></tr>`).join('')}</tbody></table>` : '<p class="small">No verified incorrect submissions in this view.</p>'}<h2>Recent attempts</h2><div style="overflow:auto"><table class="data-table"><thead><tr><th>Course ID</th><th>Step</th><th>Answer</th><th>Result</th><th>Hints / revealed</th></tr></thead><tbody>${submissions.slice(-30).reverse().map(a => `<tr><td>${escape(a.courseId)}</td><td>${escape(a.step.replaceAll('_', ' '))}</td><td>${escape(a.answer)} ${escape(a.units)}</td><td>${escape(a.result?.status || 'unresolved')}</td><td>${a.hintUsed ? 'Hint' : ''} ${a.solutionRevealed ? 'Solution shown' : ''}</td></tr>`).join('')}</tbody></table></div><div class="dialog-buttons"><button id="refresh-insights">Refresh</button><button id="export-attempts">Export these records</button></div>`;
    $('export-attempts').onclick = () => download('cv2011-attempts.json', { exportedAt: new Date().toISOString(), scope, attempts: records });
    $('refresh-insights').onclick = () => void renderInsights();
    panel.insertAdjacentHTML('beforeend', '<button id="sync-attempts">Verify and upload queued attempts for my ID</button>');
    $('sync-attempts').onclick = async () => {
        if (!online) {
            toast('Connect your course verifier first.');
            return;
        }
        let count = 0;
        for (const attempt of attempts.filter(a => !a.synced && (a.courseId === config.courseId || a.courseId === 'local-unassigned'))) {
            try {
                const response = await api('/api/attempts', { ...attempt, courseId: config.courseId, section: attempt.section ?? 0.5 });
                attempt.courseId = config.courseId;
                attempt.result = response.result;
                attempt.synced = true;
                count++;
            }
            catch (error) {
                toast(String(error));
                break;
            }
        }
        saveAttempts();
        toast(`${count} queued events verified and recorded.`);
        void renderInsights();
    };
}
for (const kind of ['pin', 'roller', 'fixed', 'guided']) {
    const icon = document.querySelector(`[data-tool="${kind}"] span`)!;
    icon.innerHTML = `<svg class="tool-icon" viewBox="-28 -4 56 44" aria-hidden="true"><g stroke="currentColor" stroke-width="2" fill="none">${supportShape(kind)}</g></svg>`;
}
// Reuse the canvas geometry so the menu and drawing show the same action
// symbols. currentColor keeps the icons legible in the selected button state.
const loadIcons: Record<string, string> = {
    force: forceSymbol(20, 35, 0, -1, 'currentColor', '', 30, 0),
    moment: momentSymbol(20, 20, 1, 'currentColor', '', 14),
    distributed: '<path d="M 5 5 H 35" fill="none" stroke="currentColor" stroke-width="1.8"/>'
        + [5, 15, 25, 35].map(x => forceSymbol(x, 35, 0, -1, 'currentColor', '', 30, 0)).join(''),
};
for (const [kind, shape] of Object.entries(loadIcons)) {
    const icon = document.querySelector(`[data-tool="${kind}"] span`)!;
    icon.innerHTML = `<svg class="tool-icon load-tool-icon" viewBox="0 0 40 40" aria-hidden="true">${shape}</svg>`;
}
fit();
setMode(location.hash.slice(1) || 'sandbox');
void connect();
void fetch('verification.json').then(r => r.json()).then(v => { proofStatus = v; }).catch(() => { });
