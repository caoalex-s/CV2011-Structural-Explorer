/** Object properties and joint constraints. Edits pass through the app's undo boundary. */
import { angleVector, endConnection, nodeLabels, position, referenceMember } from './engine.js';
import type { Analysis, Connection, ConnectionRule, Load, Member, Model } from './engine.js';
import { jointConnections, memberLabel } from './model-view.js';
import type { Selection } from './model-view.js';
import { bindDirectionDial, directionDial } from './direction-dial.js';
import { loadLabels, validLoadLabel } from './load-labels.js';
import { math, quantity } from './math.js';
import { escapeHtml as escape, formatNumber as number } from './ui.js';

// A zero force has no physical direction. Remember its editor angle until
// the next nonzero magnitude is entered on this load.
const zeroForceAngles = new WeakMap<Load, number>();
const pointAngle = (load: Load) => load.fx || load.fy
    ? Math.atan2(load.fy, load.fx) * 180 / Math.PI : zeroForceAngles.get(load) ?? 0;

// Repeated rotations must preserve the entered strength throughout a gesture.
const forceMagnitudes = new WeakMap<Load, number>();
const forceMagnitude = (load: Load) => forceMagnitudes.get(load) ?? Math.hypot(load.fx, load.fy);

const zeroMomentSenses = new WeakMap<Load, number>();
const momentSense = (load: Load) => Math.sign(load.mz) || zeroMomentSenses.get(load) || 1;

// Use the same counterclockwise turn for point and distributed load readouts.
function displayedAngle(angle: number): number {
    const remainder = angle % 360;
    return Number((remainder < 0 ? remainder + 360 : remainder).toPrecision(15)) % 360;
}

const directionArrows: Record<string, string> = {
    Down: '↓', Right: '→', Up: '↑', Left: '←', Clockwise: '↻', Counterclockwise: '↺',
};

function directionOption(key: string, value: string, label: string, current: string): string {
    const arrow = directionArrows[label];
    return `<label><input type="radio" name="${key}" data-property="${key}" value="${value}" ${value === current ? 'checked' : ''}><span>${arrow ? `<span class="choice-arrow" aria-hidden="true">${arrow}</span> ` : ''}${label}</span></label>`;
}

/** The normal follows the drawn start-to-end axis. Legacy downward-positive
 * intensity fields use 270 degrees in this editor. */
function positiveIntensityAngle(model: Model, load: Load): number {
    if (load.direction !== 'member-normal') return load.direction ?? 270;
    const a = position(model, load.member, 0), b = position(model, load.member, 1);
    return Math.atan2(b.y - a.y, b.x - a.x) * 180 / Math.PI + 90;
}

function directionPicker(load: Load, angle: number, angleInput: string, strengthInput = ''): string {
    const line = load.kind === 'distributed';
    const reference = load.direction === 'member-normal' ? 'normal' : 'global';
    const choices = line ? '<div class="direction-options dial-reference">'
        + directionOption('lineReference','global','Global',reference)
        + directionOption('lineReference','normal','Member normal',reference) + '</div>' : '';
    return `<fieldset class="load-direction-group"><legend class="${line ? '' : 'visually-hidden'}">${line ? 'Positive intensity direction' : 'Point force settings'}</legend>
        <div class="dial-layout"><div class="dial-control">${directionDial(displayedAngle(angle),line)}<span class="dial-cue">Drag to rotate</span></div><div class="dial-values">${angleInput}${choices}${strengthInput}</div></div>
        <p class="small" id="dial-help">Counterclockwise from ${math('+x')}. <span class="dial-key-help">Arrow keys adjust by 1°.</span>${line ? '<span class="visually-hidden"> Editing the angle selects Global.</span>' : ''}</p></fieldset>`;
}

interface InspectorOptions {
    container: HTMLElement;
    model: Model;
    analysis: Analysis;
    selected: Selection | null;
    resultsVisible: boolean;
    commit: (edit: () => void) => void;
    adjustLoad: (edit: () => void, first: boolean) => void;
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
            const sandbox = document.body.classList.contains('drawing-workspace');
            if (item.kind === 'force') {
                html += '<div class="load-direction-fields">'
                    + directionPicker(load, pointAngle(load),
                        angleField('pointAngle', 'Angle (°)', displayedAngle(pointAngle(load))),
                        angleField('magnitude', 'Magnitude (kN)', Number(forceMagnitude(load).toPrecision(15)))) + '</div>';
                const components = field('fx', 'Horizontal (kN)') + field('fy', 'Vertical (kN)')
                    + '<p class="small">Positive components act right and up.</p>';
                html += sandbox ? '<details class="force-components"><summary>Global components</summary>' + components + '</details>' : components;
            }
            if (item.kind === 'moment') {
                html += sandbox ? '<div class="load-direction-fields">'
                    + angleField('momentMagnitude', 'Magnitude (kN m)', Math.abs(load.mz))
                    + '<fieldset class="load-direction-group"><legend>Direction</legend><div class="direction-options">'
                    + directionOption('momentSense','-1','Clockwise',String(momentSense(load)))
                    + directionOption('momentSense','1','Counterclockwise',String(momentSense(load))) + '</div></fieldset></div>'
                    : field('mz', 'Moment, CCW + (kN m)');
            }
            if (item.kind === 'distributed') {
                const normal = load.direction === 'member-normal';
                const sign = load.direction === undefined ? -1 : 1;
                const angle = positiveIntensityAngle(model, load);
                html += field('end', 'End / member length') + '<div class="load-direction-fields">'
                    + '<div class="line-strengths"><div>' + field('fy', 'Start intensity (kN/m)', 'any', sign)
                    + '</div><div>' + field('qEnd', 'End intensity (kN/m)', 'any', sign) + '</div></div>'
                    + directionPicker(load, angle, angleField('lineAngle', 'Angle (°)', displayedAngle(angle)))
                    + '<p class="small" data-normal-help ' + (normal ? '' : 'hidden') + '>Looking from start to end, the normal points left. Editing the angle selects Global.</p>'
                    + '<p class="small">Intensity varies linearly along the member. Negative values reverse the arrows.</p></div>';
            }
            html += `<details class="inspector-help"><summary>Load notation and directions</summary><p class="small">Use ${math('P')} or ${math('F')} for a force, ${math('M')} for a couple, and ${math('w')} or ${math('q')} for distributed loading. To enter ${math('P_1')} or ${math('M_0')}, type <code>P_1</code> or <code>M_0</code>. Each load has its own label.</p><p class="small">The action belongs to this member side at a joint. Arrows retain their physical line of action; moment arcs retain their application centre.</p></details>`;
        }
        const editorKey = selected.type + ':' + selected.id;
        const expanded = container.dataset.object === editorKey && container.querySelector('details.load-settings')?.hasAttribute('open');
        const componentsOpen = container.dataset.object === editorKey && container.querySelector('details.force-components')?.hasAttribute('open');
        container.dataset.object = editorKey;
        container.innerHTML = html + '<button id="delete-selected">Delete selected object</button>';
        if (document.body.classList.contains('drawing-workspace') && selected.type === 'load') {
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
            const directions = container.querySelector('.load-direction-fields')!;
            const components = container.querySelector<HTMLDetailsElement>('.force-components');
            const settings = document.createElement('details');
            settings.className = 'load-settings';
            settings.open = !!expanded;
            settings.innerHTML = '<summary>Position and load settings</summary>';
            for (const child of [...container.children])
                if (child !== heading && child !== directions && child !== components) settings.append(child);
            if (components) components.open = !!componentsOpen;
            container.append(settings);
        }
        container.onkeydown = event => {
            const target = event.target as HTMLElement;
            if (target.matches('[data-property]') && (event.key === 'Tab' || event.key === 'Enter'))
                target.dataset.focusStep = String(event.key === 'Enter' ? 0 : event.shiftKey ? -1 : 1);
        };
        function changeProperty(input: HTMLInputElement | HTMLSelectElement, apply = commit) {
            let key = input.dataset.property!;
            let value = input.type === 'checkbox' ? (input as HTMLInputElement).checked : ['kind', 'joint', 'referenceMember', 'member', 'label', 'lineReference'].includes(key) ? input.value.trim() : Number(input.value) * Number(input.dataset.direction || 1);
            if (input.type === 'number' && (!input.value.trim() || !Number.isFinite(value) || (['magnitude', 'momentMagnitude'].includes(key) && Number(value) < 0))) {
                toast(['magnitude', 'momentMagnitude'].includes(key) ? 'Enter a finite, nonnegative magnitude.' : 'Enter a finite number.');
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
            apply(() => {
                if (key === 'pointAngle' || key === 'magnitude') {
                    const load = model.loads.find(load => load.id === selected!.id)!;
                    const angle = key === 'magnitude' ? pointAngle(load) : Number(value);
                    const magnitude = key === 'magnitude' ? Number(value) : forceMagnitude(load);
                    forceMagnitudes.set(load,magnitude);
                    const axis = angleVector(angle);
                    load.fx = magnitude * axis.x;
                    load.fy = magnitude * axis.y;
                    if (!magnitude) zeroForceAngles.set(load, angle);
                    return;
                }
                if (key === 'momentMagnitude' || key === 'momentSense') {
                    const load = model.loads.find(load => load.id === selected!.id)!;
                    const sense = key === 'momentSense' ? Number(value) : momentSense(load);
                    load.mz = sense * (key === 'momentMagnitude' ? Number(value) : Math.abs(load.mz));
                    zeroMomentSenses.set(load, sense);
                    return;
                }
                if (key === 'lineReference' || key === 'lineAngle') {
                    const load = model.loads.find(load => load.id === selected!.id)!;
                    let angle = Number(value) % 360;
                    if (value === 'global') angle = positiveIntensityAngle(model,load);
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
                if (selected?.type === 'load' && item.kind === 'force' && (key === 'fx' || key === 'fy'))
                    forceMagnitudes.delete(model.loads.find(load => load.id === selected.id)!);
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
            // Arrow keys continue within the group after a model edit rebuilds it.
            if (input.type === 'radio') {
                container.querySelector<HTMLInputElement>(`input[name="${key}"]:checked`)?.focus({preventScroll:true});
                return;
            }
            // A commit rebuilds the fields. Preserve native Tab navigation when it
            // succeeded, and restore the edited control when focus fell to the body.
            if (restoreKeyboardFocus) requestAnimationFrame(() => {
                if (document.activeElement !== document.body) return;
                const edited = container.querySelector<HTMLElement>('[data-property="' + CSS.escape(key) + '"]');
                if (!edited) return;
                const visible = [...container.querySelectorAll<HTMLElement>('input, select, button, summary, [role="slider"]')]
                    .filter(control => control.checkVisibility() && !control.matches(':disabled, input[type="radio"]:not(:checked)'));
                const next = visible[visible.indexOf(edited) + focusStep] ?? edited;
                next.focus({preventScroll:true});
            });
        }
        container.querySelectorAll<HTMLInputElement | HTMLSelectElement>('[data-property]').forEach(input =>
            input.addEventListener('change', () => changeProperty(input)));
        const dial = container.querySelector<SVGSVGElement>('.direction-dial');
        if (dial && selected.type === 'load') {
            const load = model.loads.find(load => load.id === selected.id)!;
            const exact = container.querySelector<HTMLInputElement>(load.kind === 'force' ? '[data-property="pointAngle"]' : '[data-property="lineAngle"]')!;
            bindDirectionDial(dial,(degrees,first) => {
                exact.value = String(degrees);
                changeProperty(exact, edit => options.adjustLoad(edit,first));
                if (load.kind === 'distributed') {
                    container.querySelector<HTMLInputElement>('input[name="lineReference"][value="global"]')!.checked = true;
                    container.querySelector<HTMLElement>('[data-normal-help]')!.hidden = true;
                    const sign = load.direction === undefined ? -1 : 1;
                    for (const key of ['fy','qEnd'])
                        container.querySelector<HTMLInputElement>(`[data-property="${key}"]`)!.dataset.direction = String(sign);
                } else {
                    for (const key of ['fx','fy'] as const)
                        container.querySelector<HTMLInputElement>(`[data-property="${key}"]`)!.value = String(load[key]);
                }
            });
        }
        if (selected.type === 'load' && document.body.classList.contains('drawing-workspace')) {
            const load = model.loads.find(load => load.id === selected.id)!;
            const keys = load.kind === 'distributed' ? ['fy', 'qEnd'] : [load.kind === 'moment' ? 'momentMagnitude' : 'magnitude'];
            for (const key of keys) {
                const exact = container.querySelector<HTMLInputElement>(`input[data-property="${key}"]`)!;
                const label = exact.closest('label')!;
                const slider = document.createElement('input');
                slider.type = 'range';
                slider.className = 'load-value-range';
                slider.dataset.range = key;
                slider.setAttribute('aria-label', 'Adjust ' + label.textContent!.trim().toLowerCase());
                const base = load.kind === 'distributed' ? 20 : 100;
                const bound = Math.min(Number.MAX_VALUE, Math.max(base, Math.ceil(Math.abs(Number(exact.value)) / base) * base));
                slider.min = String(load.kind === 'distributed' ? -bound : 0);
                slider.max = String(bound);
                slider.step = 'any';
                slider.value = exact.value;
                label.after(slider);

                // Keep this native input in place throughout a pointer gesture.
                // Each keyboard step forms a separate undoable edit.
                let editing = false;
                slider.oninput = () => {
                    // Round only a slider gesture. Exact entry retains its full precision.
                    const increments = load.kind === 'distributed' ? 10 : 2;
                    const rounded = Math.round(Number(slider.value) * increments) / increments;
                    if (Number.isFinite(rounded)) slider.value = String(rounded);
                    exact.value = slider.value;
                    changeProperty(exact, edit => options.adjustLoad(edit, !editing));
                    editing = true;
                    if (load.kind === 'force') {
                        for (const component of ['fx', 'fy'] as const)
                            container.querySelector<HTMLInputElement>(`[data-property="${component}"]`)!.value = String(load[component]);
                    }
                };
                const finish = () => { editing = false; };
                slider.onchange = finish;
                slider.onblur = finish;
                slider.onpointerup = finish;
                slider.onpointercancel = finish;
            }
        }
        bindConnectionEditors(container);
        container.querySelector<HTMLButtonElement>('#delete-selected')!.onclick = () => removeSelected();
    }

    inspector();
}
