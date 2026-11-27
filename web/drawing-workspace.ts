import { nodeLabels, type Model, type Sample } from './engine.js';
import { memberLabel, type Selection } from './model-view.js';
import { loadLabels } from './load-labels.js';
import { math, measureUnits, quantity } from './math.js';
import { element, formatNumber, formatSectionResult } from './ui.js';

// Native option text cannot contain typeset subscripts.
function displayLoadLabel(label: string) {
    return label.replace(/_(\d+)$/, (_, digits: string) =>
        Array.from(digits, digit => '₀₁₂₃₄₅₆₇₈₉'[Number(digit)]).join(''));
}

// Move the existing controls with their listeners intact. Mark their original
// places so the practice and instructor views keep their normal document order.
export function createDrawingWorkspace(select: (object: Selection | null) => void, inspectCut: () => void) {
    const rail = document.createElement('aside');
    rail.className = 'drawing-rail';
    rail.setAttribute('aria-label', 'Drawing inspection');
    const editor = document.createElement('section');
    editor.className = 'selection-editor';
    editor.setAttribute('aria-label', 'Object editor');
    editor.innerHTML = '<label class="object-choice">Edit object<select id="drawing-object"><option value="">Select an object</option></select></label>';
    const cutLink = document.createElement('button');
    cutLink.type = 'button';
    cutLink.className = 'inspect-object-cut';
    cutLink.onclick = inspectCut;
    const choice = editor.querySelector('label')!;
    const picker = choice.querySelector('select')!;
    let objects: Selection[] = [];
    picker.onchange = () => select(objects[picker.selectedIndex - 1] ?? null);

    const utilities = document.createElement('details');
    utilities.className = 'drawing-utilities';
    utilities.innerHTML = '<summary>Workspace menu</summary>';
    const title = document.createElement('header');
    title.className = 'drawing-title';
    title.innerHTML = '<h2></h2><span></span>';
    const emptyActions = document.createElement('div');
    emptyActions.className = 'empty-drawing-actions';
    emptyActions.innerHTML = '<button type="button">Draw member</button> <button type="button">Open beam example</button>';
    emptyActions.children[0].addEventListener('click', () => document.querySelector<HTMLButtonElement>('[data-tool="member"]')!.click());
    emptyActions.children[1].addEventListener('click', () => {
        element<HTMLSelectElement>('preset').value = 'beam';
        element('load-preset').click();
    });
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
        const canvas = element('canvas');
        const tools = find('.left-panel');
        if (compact.matches) {
            canvas.before(tools);
            canvas.after(editor, cutReadout, find('.section-response'));
        } else {
            canvas.after(tools, find('.response-toolbar'), find('.canvas-header'));
            cutReadout.remove();
            rail.insertBefore(find('.section-response'), rail.querySelector('.support-reactions'));
            rail.prepend(editor);
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
            editor.remove();
            emptyActions.remove(); document.body.classList.remove('empty-drawing');
            rail.remove(); cutReadout.remove(); title.remove(); sectionTitle.remove(); utilities.remove();
            for (const disclosure of [directory, files, toolbox]) disclosure.open = !matchMedia('(max-width:750px)').matches;
            return;
        }
        const panel = find('.canvas-panel');
        const actions = find('.header-actions');
        actions.before(utilities);
        move(actions, utilities);
        panel.prepend(title, emptyActions);
        move(find('.left-panel'), panel, title.nextSibling);
        find('.work-grid').append(rail);
        move(find('.right-panel'), editor);
        editor.append(cutLink);
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
    function update(model: Model, selected: Selection | null, sample: Sample | undefined, stationMath: string[], face: string) {
        if (!active) return;
        cutLink.hidden = !selected || selected.type === 'node';
        cutLink.textContent = selected?.type === 'member' ? 'Inspect member cut' :
            model.loads.some(load => selected?.type === 'load' && load.id === selected.id && load.kind === 'distributed')
                ? 'Inspect cut at load start' : 'Inspect cut here';
        document.body.classList.toggle('empty-drawing', model.members.length === 0);
        title.querySelector('h2')!.textContent = model.members.length ? element('response-title').textContent : 'Draw a structure';
        title.querySelector('span')!.textContent = `${model.nodes.length} joints · ${model.members.length} ${model.members.length === 1 ? 'member' : 'members'}`;
        cutReadout.hidden = !sample;
        if (sample) {
            const sign = (value: number) => (value > 1e-7 ? '+' : '') + formatSectionResult(value);
            const shear = math('V = ' + quantity(sign(sample.V), measureUnits.force));
            const moment = math('M = ' + quantity(sign(sample.M), measureUnits.moment));
            cutReadout.innerHTML = [...stationMath, ...(face ? [`<span>${face}</span>`] : []), shear, moment].join(' ');
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
