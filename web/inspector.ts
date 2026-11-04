/** Object properties and joint constraints. Edits pass through the app's undo boundary. */
import { endConnection, nodeLabels, position, referenceMember } from './engine.js';
import type { Analysis, Connection, ConnectionRule, Load, Member, Model } from './engine.js';
import { jointConnections, memberLabel } from './model-view.js';
import type { Selection } from './model-view.js';
import { loadLabels, validLoadLabel } from './load-labels.js';
import { escapeHtml as escape, formatNumber as number } from './ui.js';

interface InspectorOptions {
    container: HTMLElement;
    model: Model;
    analysis: Analysis;
    selected: Selection | null;
    resultsVisible: boolean;
    commit: (edit: () => void) => void;
    clearSelection: () => void;
    removeSelected: () => void;
    projectToMember: (point: { x: number; y: number }, member: Member) => { t: number };
    notify: (message: string) => void;
}

/** Render the selected object and bind handlers to this render's model snapshot. */
export function renderInspector(options: InspectorOptions): void {
    const { container, model, analysis, selected, resultsVisible, commit,
        clearSelection, removeSelected, projectToMember, notify: toast } = options;
    function connectionEditor(member: Member, end: 'a' | 'b'): string {
        const node = model.nodes.find(node => node.id === member[end])!;
        const label = `${memberLabel(model, member)} at ${nodeLabels(model).get(node.id)}`;
        if (referenceMember(model, node.id) === member.id) return `<p class="small"><b>${label}</b>: reference side</p>`;
        const connection = endConnection(model, member, end);
        const rows = (['axial', 'transverse', 'rotation'] as const).map(direction => {
            const value = connection[direction], name = direction === 'axial' ? 'Axial N / local x' : direction === 'transverse' ? 'Shear V / local y' : 'Moment M / rotation';
            const attributes = `data-connection-member="${escape(member.id)}" data-end="${end}" data-direction="${direction}"`;
            return `<label class="field">${name}<select ${attributes} aria-label="${name}: ${label}">${[['rigid', 'Continuous'], ['free', 'Released'], ['spring', 'Elastic spring']].map(([key, caption]) => `<option value="${key}" ${key === (typeof value === 'number' ? 'spring' : value) ? 'selected' : ''}>${caption}</option>`).join('')}</select></label>${typeof value === 'number' ? `<label class="field">Stiffness (${direction === 'rotation' ? 'kN m/rad' : 'kN/m'})<input type="number" min="0" step="any" value="${value}" ${attributes} data-stiffness="true" aria-label="${direction} stiffness: ${label}"></label>` : ''}`;
        }).join('');
        const result = analysis.connections?.find(item => item.member === member.id && item.end === end);
        const response = result && (resultsVisible) ? `<p class="small">Relative rotation Δθ = ${number(result.relativeRotation)} rad<br>Axial slip = ${number(result.axialSlip * 1000)} mm<br>Transverse slip = ${number(result.transverseSlip * 1000)} mm</p>` : '';
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
                for (const item of jointConnections(model, node)) {
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
        if (!selected) {
            container.innerHTML = '<p class="small">Select an object to edit its position, loading, or stiffness.</p>';
            return;
        }
        const collection = selected.type === 'node' ? model.nodes : selected.type === 'member' ? model.members : selected.type === 'support' ? model.supports : model.loads;
        const item = collection.find(i => i.id === selected!.id) as unknown as Record<string, string | number>;
        if (!item) {
            clearSelection();
            return;
        }
        // Load intensity is presented downward-positive as in Tutorial 5. Stored
        // force components remain upward-positive for model-file compatibility.
        const field = (key: string, label: string, step = 'any', direction = 1) => `<label class="field">${label}<input type="number" data-property="${key}" data-direction="${direction}" value="${Number(item[key] ?? (key === 'rotationStiffness' ? 20000 : 0)) * direction}" step="${step}"></label>`;
        let html = `<h3>${escape(selected.type[0].toUpperCase() + selected.type.slice(1))} properties</h3>`;
        if (selected.type === 'load' || selected.type === 'support') html += `<label class="field">Attached member<select data-property="member">${model.members.map(member => `<option value="${escape(member.id)}" ${member.id === item.member ? 'selected' : ''}>${memberLabel(model, member)}</option>`).join('')}</select></label>`;
        if (selected.type === 'node') {
            const node = model.nodes.find(node => node.id === selected!.id)!;
            const connected = jointConnections(model, node), reference = referenceMember(model, node.id);
            html += `<p class="small">Node <b>${nodeLabels(model).get(node.id)}</b> · labels update automatically when nodes are added or removed.</p>` + field('x', 'x (m)') + field('y', 'y (m)');
            const jointNames: Record<string, string> = { rigid: 'Rigid joint', pinned: 'Internal pin / hinge', 'semi-rigid': 'Semi-rigid joint', custom: 'Member-specific constraints' };
            html += `<label class="field">Joint connection<select data-property="joint">${Object.entries(jointNames).map(([kind, label]) => `<option value="${kind}" ${kind === (node.joint || 'rigid') ? 'selected' : ''}>${label}</option>`).join('')}</select></label>`;
            if (node.joint === 'semi-rigid') html += field('rotationStiffness', 'Rotational stiffness kθ (kN m/rad)');
            if (connected.length > 1) html += `<label class="field">Reference member<select data-property="referenceMember">${connected.map(({ member }) => `<option value="${escape(member.id)}" ${member.id === reference ? 'selected' : ''}>${memberLabel(model, member)}</option>`).join('')}</select></label><p class="small">Connections relate each other member end to this reference. A pin shares translations and permits relative rotation. A rotational spring transfers moment M = kθ Δθ.</p>${connected.map(({ member, end }) => connectionEditor(member, end)).join('')}`;
            else html += '<p class="small">A joint connection relates two or more members. At a single-member end, use a ground support to constrain movement.</p>';
        }
        if (selected.type === 'member') {
            const member = model.members.find(member => member.id === selected!.id)!;
            html += `<p class="small">Member <b>${memberLabel(model, member)}</b></p>` + field('EA', 'Axial rigidity EA (kN)') + field('EI', 'Flexural rigidity EI (kN m²)');
            html += connectionEditor(member, 'a') + connectionEditor(member, 'b');
        }
        if (selected.type === 'support')
            html += `<label class="field">Support type<select data-property="kind">${['pin', 'roller', 'fixed', 'guided', 'custom'].map(k => `<option ${item.kind === k ? 'selected' : ''}>${k}</option>`).join('')}</select></label>` + field('t', 'Position / member length', '0.01') + (['roller', 'guided'].includes(String(item.kind)) ? field('angle', 'Restrained translation angle from +x (°)') : '') + (item.kind === 'custom' ? [['fixX', 'Restrain global x'], ['fixY', 'Restrain global y'], ['fixRotation', 'Restrain rotation θ']].map(([key, label]) => `<label class="check"><input type="checkbox" data-property="${key}" ${item[key] ? 'checked' : ''}>${label}</label>`).join('') : '') + '<p class="small">Ground restraints act on the selected member side. A pin support does not release continuity between connected members.</p>';
        if (selected.type === 'load') {
            html += `<label class="field">Load label<input type="text" data-property="label" maxlength="10" value="${escape(loadLabels(model).get(selected.id))}" placeholder="${item.kind === 'moment' ? 'M_0' : item.kind === 'distributed' ? 'w_1' : 'P_1'}"></label>`;
            html += field('t', 'Start / member length', '0.01');
            if (item.kind === 'force')
                html += field('fx', 'Horizontal force Fx, rightward + (kN)') + field('fy', 'Vertical force Fy, upward + (kN)');
            if (item.kind === 'moment')
                html += field('mz', 'Moment, CCW + (kN m)');
            if (item.kind === 'distributed')
                html += field('end', 'End / member length', '0.01') + field('fy', 'Start intensity w, downward + (kN/m)', 'any', -1) + field('qEnd', 'End intensity w, downward + (kN/m)', 'any', -1);
            html += '<details class="inspector-help"><summary>Load notation and directions</summary><p class="small">Use P or F for a force, M for a couple, and w or q for distributed loading. An optional subscript uses an underscore, for example P_1 or M_0. Each load has its own label.</p><p class="small">The action belongs to this member side at a joint. Arrows retain their physical line of action; moment arcs retain their application centre.</p></details>';
        }
        container.innerHTML = html + '<button id="delete-selected">Delete selected object</button>';
        container.querySelectorAll<HTMLInputElement | HTMLSelectElement>('[data-property]').forEach(input => input.addEventListener('change', () => {
            const key = input.dataset.property!;
            const value = input.type === 'checkbox' ? (input as HTMLInputElement).checked : ['kind', 'joint', 'referenceMember', 'member', 'label'].includes(key) ? input.value.trim() : Number(input.value) * Number(input.dataset.direction || 1);
            if (key === 'label' && (!validLoadLabel(String(value), item.kind as Load['kind']) || model.loads.some(load => load.id !== selected!.id && loadLabels(model).get(load.id) === value))) {
                toast('Enter a unique load symbol, such as P_1, M_0, or w_1.');
                inspector();
                return;
            }
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
                const previousConnections = selected?.type === 'node' && key === 'joint' ? jointConnections(model, model.nodes.find(node => node.id === selected!.id)!) : [];
                if (key === 'member') {
                    const point = position(model, String(item.member), Number(item.t));
                    const next = model.members.find(member => member.id === value)!;
                    const projected = projectToMember(point, next);
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
        container.querySelector<HTMLButtonElement>('#delete-selected')!.onclick = () => removeSelected();
    }

    inspector();
}
