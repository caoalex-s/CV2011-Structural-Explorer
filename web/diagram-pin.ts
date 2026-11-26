import { analyse, position, type Analysis, type Model, type Sample } from './engine.js';
import { loadLabels, loadLabelText } from './load-labels.js';
import { sampleSection } from './responses.js';
import { formatNumber, formatSectionResult } from './ui.js';

export type DiagramField = 'M' | 'V' | 'N' | 'displacement';
export function isDiagramField(field: string): field is DiagramField {
    return ['M', 'V', 'N', 'displacement'].includes(field);
}
const titles = { M: 'bending moment', V: 'shear force', N: 'axial force', displacement: 'deflected shape' };
const units = { M: 'kN·m', V: 'kN', N: 'kN', displacement: 'mm' };

function geometry(model: Model) {
    // Releases, loads, restraints and stiffness can change on the same geometry.
    // Member orientation matters because it defines local axes and cut faces.
    const ordered = <T extends {id: string}>(items: T[]) => [...items].sort((a,b) => a.id.localeCompare(b.id));
    return JSON.stringify([ordered(model.nodes).map(n => [n.id,n.x,n.y]),
        ordered(model.members).map(m => [m.id,m.a,m.b])]);
}
function sourceLabel(model: Model) {
    if (model.loads.length !== 1) return model.loads.length + ' applied loads';
    const load = model.loads[0], label = loadLabelText(loadLabels(model).get(load.id)!);
    if (load.kind === 'moment') return label + ' = ' + formatNumber(load.mz) + ' kN·m';
    if (load.kind === 'distributed') return label + ' · distributed load';
    const angle = Math.atan2(load.fy,load.fx) * 180 / Math.PI;
    const direction = load.fx === 0 ? (load.fy < 0 ? 'down' : 'up') : formatNumber(angle) + '°';
    return label + ' · ' + formatNumber(Math.hypot(load.fx,load.fy)) + ' kN ' + direction;
}
export function amplitude(sample: Sample, field: DiagramField) {
    return field === 'displacement' ? Math.hypot(sample.ux,sample.uy) : Math.abs(sample[field]);
}

export function createDiagramPin(storageKey: string) {
    function snapshot(model: Model, field: DiagramField) {
        const source = structuredClone(model);
        const analysis = analyse(source);
        if (analysis.status !== 'stable' || !analysis.elements.length) return;
        const peak = Math.max(...analysis.elements.flatMap(e => e.samples.map(p => amplitude(p,field))));
        return {model:source, field, analysis, geometry:geometry(source), peak};
    }
    let pinned: ReturnType<typeof snapshot>;
    try {
        const saved = JSON.parse(sessionStorage.getItem(storageKey) || 'null');
        if (saved && isDiagramField(saved.field)) pinned = snapshot(saved.model,saved.field);
    } catch { /* A stale tab snapshot cannot supply a comparison. */ }
    const button = document.getElementById('pin-diagram') as HTMLButtonElement;
    const buttonHome = button.parentElement!;
    const panel = document.getElementById('diagram-comparison')!;
    function toggle(model: Model, layer: string) {
        if (pinned) { pinned = undefined; sessionStorage.removeItem(storageKey); }
        else if (isDiagramField(layer)) {
            pinned = snapshot(model,layer);
            if (pinned) sessionStorage.setItem(storageKey,JSON.stringify({model:pinned.model,field:layer}));
        }
    }
    function update(active: boolean, model: Model, analysis: Analysis, layer: string, member: string, t: number, side: 'left'|'right') {
        // Keep Clear pin reachable even when an empty canvas hides its toolbar.
        const parent = active && pinned ? panel : buttonHome;
        if (button.parentElement !== parent) {
            const restoreFocus = document.activeElement === button;
            parent.prepend(button);
            if (restoreFocus) requestAnimationFrame(() => button.focus({preventScroll:true}));
        }
        button.hidden = !active;
        panel.hidden = !active || !pinned;
        if (!active) return;
        const available = analysis.status === 'stable' && analysis.elements.length > 0 && isDiagramField(layer);
        button.textContent = pinned ? 'Clear pin' : 'Pin diagram';
        button.disabled = !pinned && !available;
        button.title = available || pinned ? '' : 'Choose a solved response diagram to pin.';
        if (!pinned) return;
        let reason = '';
        if (pinned.field !== layer) reason = 'Select ' + titles[pinned.field] + ' to compare this pin.';
        else if (!available) reason = 'Comparison paused. The current drawing has no stable numerical solution.';
        else if (geometry(model) !== pinned.geometry) reason = 'Comparison paused. Member geometry or orientation has changed.';
        const fields = (id: string, value: string) => { document.getElementById(id)!.textContent = value; };
        const result = (drawing: Model, solution: Analysis) => {
            const sample = sampleSection(solution,member,t,side,drawing);
            if (!sample) return 'Cut value unavailable';
            const field = pinned!.field;
            const value = field === 'displacement' ? 1000 * Math.hypot(sample.ux,sample.uy) : sample[field];
            return (field === 'displacement' ? '|u|' : field) + ' = ' + formatSectionResult(value) + ' ' + units[field];
        };
        fields('pin-reference',sourceLabel(pinned.model) + (reason ? '' : ' · ' + result(pinned.model,pinned.analysis)));
        fields('pin-current',sourceLabel(model) + (reason ? '' : ' · ' + result(model,analysis)));
        const station = model.members.find(m => m.id === member);
        if (!reason && station) {
            const a = position(model,member,0), b = position(model,member,1);
            fields('pin-status','Numerical ' + titles[pinned.field] + ' · shared scale · ' + member + ', x = ' +
                formatNumber(t*Math.hypot(b.x-a.x,b.y-a.y)) + ' m, just ' + side);
        } else fields('pin-status',reason);
        fields('pin-reference-source',JSON.stringify(pinned.model,null,2));
        fields('pin-current-source',JSON.stringify(model,null,2));
        return reason ? undefined : pinned;
    }
    return {toggle,update};
}
