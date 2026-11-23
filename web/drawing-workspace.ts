import { nodeLabels, type Model, type Sample } from './engine.js';
import { memberLabel, type Selection } from './model-view.js';
import { loadLabels } from './load-labels.js';
import { element, formatNumber } from './ui.js';

// Native option text cannot contain typeset subscripts.
function displayLoadLabel(label: string) {
    return label.replace(/_(\d+)$/, (_, digits: string) =>
        Array.from(digits, digit => '₀₁₂₃₄₅₆₇₈₉'[Number(digit)]).join(''));
}

// Move the existing controls with their listeners intact. Mark their original
// places so the practice and instructor views keep their normal document order.
export function createDrawingWorkspace(select: (object: Selection | null) => void) {
    const rail = document.createElement('aside');
    rail.className = 'drawing-rail';
    rail.setAttribute('aria-label', 'Drawing inspection');
    rail.innerHTML = '<h2>Drawing properties</h2><label class="object-choice">Object<select id="drawing-object"><option value="">Select an object</option></select></label>';
    const choice = rail.querySelector('label')!;
    const picker = choice.querySelector('select')!;
    let objects: Selection[] = [];
    picker.onchange = () => select(objects[picker.selectedIndex - 1] ?? null);

    const utilities = document.createElement('details');
    utilities.className = 'drawing-utilities';
    utilities.innerHTML = '<summary>Workspace menu</summary>';
    const title = document.createElement('header');
    title.className = 'drawing-title';
    title.innerHTML = '<h2></h2><span></span>';
    const cutReadout = document.createElement('div');
    cutReadout.className = 'cut-readout';
    cutReadout.setAttribute('aria-live','polite');
    const sectionTitle = document.createElement('h3');
    sectionTitle.textContent = 'Section response';
    const origins = new Map<Element, Comment>();
    const find = (selector: string) => document.querySelector<HTMLElement>(selector)!;
    function move(node: HTMLElement, parent: HTMLElement, before: ChildNode | null = null) {
        const marker = document.createComment('workspace control');
        node.before(marker);
        origins.set(node, marker);
        parent.insertBefore(node, before);
    }
    const toolbox = element<HTMLDetailsElement>('drawing-toolbox');
    const directory = find('.exercise-directory') as HTMLDetailsElement;
    const files = find('.model-files') as HTMLDetailsElement;
    const compact = matchMedia('(max-width:750px)');
    let active = false;
    function arrangeInspector() {
        if (!active) return;
        const properties = find('.right-panel');
        const canvas = element('canvas');
        const tools = find('.left-panel');
        if (compact.matches) {
            canvas.before(tools);
            canvas.after(cutReadout, choice, properties, find('.section-response'));
        } else {
            canvas.after(tools, find('.response-toolbar'), find('.canvas-header'));
            cutReadout.remove();
            rail.insertBefore(find('.section-response'), rail.querySelector('.support-reactions'));
            rail.insertBefore(choice, rail.querySelector('.section-response'));
            choice.after(properties);
        }
    }
    compact.addEventListener('change', arrangeInspector);
    const menus = [directory, files, utilities];
    document.addEventListener('click', event => {
        const command = (event.target as Element).closest('button,a');
        if (active && command) for (const menu of menus)
            if (menu.contains(command)) menu.open = false;
    });
    document.addEventListener('pointerdown', event => {
        if (!active) return;
        for (const menu of menus)
            if (menu.open && !menu.contains(event.target as Node)) menu.open = false;
    });
    document.addEventListener('keydown', event => {
        if (!active || event.key !== 'Escape') return;
        const menu = menus.find(item => item.open && item.contains(document.activeElement));
        if (menu) {
            menu.open = false;
            menu.querySelector('summary')!.focus();
        }
    });
    function activate(enabled: boolean) {
        if (enabled === active) return;
        active = enabled;
        document.body.classList.toggle('drawing-workspace', active);
        if (!active) {
            for (const [node, marker] of origins) marker.replaceWith(node);
            origins.clear();
            rail.append(choice);
            rail.remove(); cutReadout.remove(); title.remove(); sectionTitle.remove(); utilities.remove();
            for (const disclosure of [directory, files, toolbox]) disclosure.open = !matchMedia('(max-width:750px)').matches;
            return;
        }
        const panel = find('.canvas-panel');
        const actions = find('.header-actions');
        actions.before(utilities);
        move(actions, utilities);
        panel.prepend(title);
        move(find('.left-panel'), panel, title.nextSibling);
        find('.work-grid').append(rail);
        move(find('.right-panel'), rail);
        const nav = find('.topbar nav');
        for (const mode of ['practice','insights']) move(nav.querySelector('[data-mode="' + mode + '"]')!, actions);
        const response = find('.section-response');
        move(response, rail);
        response.prepend(sectionTitle);
        const note = document.getElementById('frame-overview-convention');
        if (note) move(note, response);
        move(element('section-free-body'), panel);
        move(find('.support-reactions'), rail);
        arrangeInspector();
        directory.open = files.open = false;
        toolbox.open = !matchMedia('(max-width:750px)').matches;
        for (const button of toolbox.querySelectorAll('button[data-tool]'))
            button.setAttribute('title', button.textContent!.trim());
    }
    function update(model: Model, selected: Selection | null, sample: Sample | undefined, station: string, face: string) {
        if (!active) return;
        rail.querySelector('h2')!.hidden = compact.matches;
        title.querySelector('h2')!.textContent = element('response-title').textContent;
        title.querySelector('span')!.textContent = `${model.nodes.length} joints · ${model.members.length} ${model.members.length === 1 ? 'member' : 'members'}`;
        cutReadout.hidden = !sample;
        if (sample) {
            const sign = (value: number) => (value > 1e-7 ? '+' : '') + formatNumber(value);
            cutReadout.textContent = station + (face ? ' · ' + face : '') + '   ·   V = ' + sign(sample.V) + ' kN   ·   M = ' + sign(sample.M) + ' kN·m';
        }
        const nodes = nodeLabels(model), loads = loadLabels(model);
        const entries = [
            ...model.loads.map(l => ({type:'load', id:l.id, name:`${displayLoadLabel(loads.get(l.id)!)} · ${l.kind === 'force' ? 'Point force' : l.kind === 'moment' ? 'Applied moment' : 'Distributed load'}`})),
            ...model.members.map(m => ({type:'member', id:m.id, name:`Member ${memberLabel(model,m)}`})),
            ...model.nodes.map(n => ({type:'node', id:n.id, name:`Joint ${nodes.get(n.id)}`})),
            ...model.supports.map(s => ({type:'support', id:s.id, name:`${s.kind} support · ${memberLabel(model,model.members.find(m => m.id === s.member)!)} at t = ${formatNumber(s.t)}`}))
        ];
        objects = entries;
        picker.replaceChildren(new Option('Select an object',''), ...entries.map(e => new Option(e.name, e.type + ':' + e.id)));
        picker.selectedIndex = entries.findIndex(e => e.id === selected?.id && e.type === selected.type) + 1;
    }
    return { activate, update };
}
