/** Object properties and joint constraints. Edits pass through the app's undo boundary. */
import { angleVector, endConnection, nodeLabels, position, referenceMember } from './engine.js';
import type { Analysis, Connection, ConnectionRule, Load, Member, Model } from './engine.js';
import { jointConnections, memberLabel } from './model-view.js';
import type { Selection } from './model-view.js';
import { loadLabels, validLoadLabel } from './load-labels.js';
import { math, quantity } from './math.js';
import { escapeHtml as escape, formatNumber as number } from './ui.js';

// A zero force has no physical direction. Remember its editor angle until
// the next nonzero magnitude is entered on this load.
const zeroForceAngles = new WeakMap<Load, number>();
const pointAngle = (load: Load) => load.fx || load.fy
    ? Math.atan2(load.fy, load.fx) * 180 / Math.PI : zeroForceAngles.get(load) ?? 0;

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
        const response = result && resultsVisible ? `<p class="small">Relative rotation ${math('\\Delta\\theta = ' + quantity(number(result.relativeRotation), '\\mathrm{rad}'))}<br>Axial slip = ${number(result.axialSlip * 1000)} mm<br>Transverse slip = ${number(result.transverseSlip * 1000)} mm</p>` : '';
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
                if (input.value.trim() === '' || !Number.isFinite(value) || value < 0 || (direction !== 'rotation' && value === 0)) { toast('Use a positive spring stiffness, or choose Released.'); inspector(); return; }
                if (direction === 'rotation' && value === 0) value = 'free';
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
            html += `<p class="small">Node <b>${nodeLabels(model).get(node.id)}</b> · labels update automatically when nodes are added or removed.</p>` + field('x', math('x') + ' (m)') + field('y', math('y') + ' (m)');
            const jointNames: Record<string, string> = { rigid: 'Rigid joint', pinned: 'Internal pin / hinge', 'semi-rigid': 'Semi-rigid joint', custom: 'Member-specific constraints' };
            html += `<label class="field">Joint connection<select data-property="joint">${Object.entries(jointNames).map(([kind, label]) => `<option value="${kind}" ${kind === (node.joint || 'rigid') ? 'selected' : ''}>${label}</option>`).join('')}</select></label>`;
            if (node.joint === 'semi-rigid') html += field('rotationStiffness', `Rotational stiffness ${math('k_\\theta')} (kN m/rad)`);
            if (connected.length > 1) html += `<label class="field">Reference member<select data-property="referenceMember">${connected.map(({ member }) => `<option value="${escape(member.id)}" ${member.id === reference ? 'selected' : ''}>${memberLabel(model, member)}</option>`).join('')}</select></label><p class="small">Connections relate each other member end to this reference. A pin shares translations and permits relative rotation. A rotational spring transfers moment ${math(String.raw`M=k_\theta\Delta\theta`)}.</p>${connected.map(({ member, end }) => connectionEditor(member, end)).join('')}`;
            else html += '<p class="small">A joint connection relates two or more members. At a single-member end, use a ground support to constrain movement.</p>';
        }
        if (selected.type === 'member') {
            const member = model.members.find(member => member.id === selected!.id)!;
            html += `<p class="small">Member <b>${memberLabel(model, member)}</b></p>`
                + field('EA', `Axial rigidity ${math('EA')} (kN)`)
                + field('EI', `Flexural rigidity ${math('EI')} (${math('\\mathrm{kN}\\,\\mathrm{m}^2')})`);
            html += connectionEditor(member, 'a') + connectionEditor(member, 'b');
        }
        if (selected.type === 'support')
            html += `<label class="field">Support type<select data-property="kind">${['pin', 'roller', 'fixed', 'guided', 'custom'].map(k => `<option ${item.kind === k ? 'selected' : ''}>${k}</option>`).join('')}</select></label>` + field('t', 'Position / member length', '0.01') + (['roller', 'guided'].includes(String(item.kind)) ? field('angle', `Restrained translation angle from ${math('+x')} (°)`) : '') + (item.kind === 'custom' ? [['fixX', `Restrain global ${math('x')}`], ['fixY', `Restrain global ${math('y')}`], ['fixRotation', `Restrain rotation ${math('\\theta')}`]].map(([key, label]) => `<label class="check"><input type="checkbox" data-property="${key}" ${item[key] ? 'checked' : ''}>${label}</label>`).join('') : '') + '<p class="small">Ground restraints act on the selected member side. A pin support does not release continuity between connected members.</p>';
        if (selected.type === 'load') {
            html += `<label class="field">Load label<input type="text" data-property="label" maxlength="10" value="${escape(loadLabels(model).get(selected.id))}" placeholder="${item.kind === 'moment' ? 'M_0' : item.kind === 'distributed' ? 'w_1' : 'P_1'}"></label>`;
            html += field('t', 'Start / member length', 'any');
            const load = model.loads.find(load => load.id === selected.id)!;
            const angleField = (key: string, caption: string, value: number) =>
                `<label class="field">${caption}<input type="number" step="any" data-property="${key}" value="${value}"></label>`;
            if (item.kind === 'force') {
                html += '<div class="load-direction-fields">'
                    + angleField('magnitude', 'Magnitude (kN)', Number(Math.hypot(load.fx, load.fy).toPrecision(15)))
                    + angleField('pointAngle', `Angle CCW from global ${math('+x')} (°)`, Number(pointAngle(load).toPrecision(15))) + '</div>';
                html += field('fx', `Horizontal force ${math('F_x')}, rightward + (kN)`) + field('fy', `Vertical force ${math('F_y')}, upward + (kN)`);
            }
            if (item.kind === 'moment')
                html += field('mz', 'Moment, CCW + (kN m)');
            if (item.kind === 'distributed') {
                const normal = load.direction === 'member-normal';
                const sign = load.direction === undefined ? -1 : 1;
                html += field('end', 'End / member length') + field('fy', 'Start intensity (kN/m)', 'any', sign)
                    + '<div class="load-direction-fields">' + field('qEnd', 'End intensity (kN/m)', 'any', sign)
                    + `<label class="field">Positive direction<select data-property="lineReference"><option value="global">Global angle</option><option value="normal" ${normal ? 'selected' : ''}>Member normal (+local y)</option></select></label>`
                    + (normal ? '' : angleField('lineAngle',`Angle CCW from global ${math('+x')} (°)`, Number(load.direction ?? 270)))
                    + '<p class="small">Intensities vary linearly per metre of member length. A negative value reverses the arrow. The positive member normal points left when looking from the first joint to the second.</p></div>';
            }
            html += `<details class="inspector-help"><summary>Load notation and directions</summary><p class="small">Use ${math('P')} or ${math('F')} for a force, ${math('M')} for a couple, and ${math('w')} or ${math('q')} for distributed loading. To enter ${math('P_1')} or ${math('M_0')}, type <code>P_1</code> or <code>M_0</code>. Each load has its own label.</p><p class="small">The action belongs to this member side at a joint. Arrows retain their physical line of action; moment arcs retain their application centre.</p></details>`;
        }
        const editorKey = selected.type + ':' + selected.id;
        const expanded = container.dataset.object === editorKey && container.querySelector('details.load-settings')?.hasAttribute('open');
        container.dataset.object = editorKey;
        container.innerHTML = html + '<button id="delete-selected">Delete selected object</button>';
        if (document.body.classList.contains('drawing-workspace') && selected.type === 'load') {
            const principal = container.querySelector<HTMLInputElement>(item.kind === 'moment' ? '[data-property="mz"]' : '[data-property="fy"]');
            const heading = container.querySelector('h3')!;
            const label = loadLabels(model).get(selected.id)!;
            heading.textContent = (item.kind === 'force' ? 'Point force' : item.kind === 'moment' ? 'Applied moment' : 'Distributed load') + ' · ';
            const [symbol, subscript] = label.split('_');
            const notation = document.createElement('i');
            notation.textContent = symbol;
            if (subscript) {
                const index = document.createElement('sub');
                index.textContent = subscript;
                notation.append(index);
            }
            heading.append(notation);
            const primaryField = principal?.closest('label');
            if (primaryField) {
                primaryField.classList.add('principal-field');
                heading.after(primaryField);
                const settings = document.createElement('details');
                settings.className = 'load-settings';
                settings.open = !!expanded;
                settings.innerHTML = '<summary>Position and load settings</summary>';
                while (primaryField.nextElementSibling) settings.append(primaryField.nextElementSibling);
                primaryField.after(settings);
                const directions = settings.querySelector('.load-direction-fields');
                if (directions) primaryField.after(directions);
            }
        }
        container.onkeydown = event => {
            const target = event.target as HTMLElement;
            if (target.matches('[data-property]') && (event.key === 'Tab' || event.key === 'Enter'))
                target.dataset.focusStep = String(event.key === 'Enter' ? 0 : event.shiftKey ? -1 : 1);
        };
        container.querySelectorAll<HTMLInputElement | HTMLSelectElement>('[data-property]').forEach(input => input.addEventListener('change', () => {
            let key = input.dataset.property!;
            let value = input.type === 'checkbox' ? (input as HTMLInputElement).checked : ['kind', 'joint', 'referenceMember', 'member', 'label', 'lineReference'].includes(key) ? input.value.trim() : Number(input.value) * Number(input.dataset.direction || 1);
            if (input.type === 'number' && (!input.value.trim() || !Number.isFinite(value) || (key === 'magnitude' && Number(value) < 0))) {
                toast(key === 'magnitude' ? 'Enter a finite, nonnegative magnitude.' : 'Enter a finite number.');
                inspector();
                return;
            }
            if (key === 'rotationStiffness') {
                if (input.value.trim() === '' || Number(value) < 0) { toast('Enter a nonnegative rotational stiffness.'); inspector(); return; }
                if (value === 0) { key = 'joint'; value = 'pinned'; }
            }
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
            const focusStep = Number(input.dataset.focusStep || 0);
            const restoreKeyboardFocus = (input.dataset.focusStep !== undefined || input.matches(':focus-visible')) && document.body.classList.contains('drawing-workspace');
            commit(() => {
                if (key === 'pointAngle' || key === 'magnitude') {
                    const load = model.loads.find(load => load.id === selected!.id)!;
                    const angle = key === 'pointAngle' ? Number(value) : pointAngle(load);
                    const magnitude = key === 'magnitude' ? Number(value) : Math.hypot(load.fx, load.fy);
                    const axis = angleVector(angle);
                    load.fx = magnitude * axis.x;
                    load.fy = magnitude * axis.y;
                    if (!magnitude) zeroForceAngles.set(load, angle);
                    return;
                }
                if (key === 'lineReference' || key === 'lineAngle') {
                    const load = model.loads.find(load => load.id === selected!.id)!;
                    const angle = key === 'lineAngle' ? Number(value) % 360 : 270;
                    const direction = value === 'normal' ? 'member-normal' : angle === 270 || angle === -90 ? undefined : angle;
                    // Preserve the displayed start and end strengths. A legacy
                    // downward reference stores them as global upward components.
                    if ((load.direction === undefined) !== (direction === undefined)) {
                        load.fy = -load.fy;
                        load.qEnd = -load.qEnd;
                    }
                    if (direction === undefined) delete load.direction;
                    else load.direction = direction;
                    return;
                }
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
            // A commit rebuilds the fields. Preserve native Tab navigation when it
            // succeeded, and restore the edited control when focus fell to the body.
            if (restoreKeyboardFocus) requestAnimationFrame(() => {
                if (document.activeElement !== document.body) return;
                const edited = container.querySelector<HTMLElement>('[data-property="' + CSS.escape(key) + '"]');
                if (!edited) return;
                const visible = [...container.querySelectorAll<HTMLElement>('input, select, button, summary')]
                    .filter(control => control.checkVisibility() && !control.matches(':disabled'));
                const next = visible[visible.indexOf(edited) + focusStep] ?? edited;
                next.focus({preventScroll:true});
            });
        }));
        bindConnectionEditors(container);
        container.querySelector<HTMLButtonElement>('#delete-selected')!.onclick = () => removeSelected();
    }

    inspector();
}
