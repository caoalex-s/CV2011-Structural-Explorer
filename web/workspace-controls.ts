/** Drawing and response controls. Callbacks leave model state with the application. */
import { forceSymbol, momentSymbol, supportShape } from './symbols.js';
import { element } from './ui.js';

interface ControlActions {
    selectTool: (tool: string) => void;
    selectLayer: (layer: string) => void;
    selectMode: (mode: string) => void;
}

/** Keep visual selection and accessible pressed state together for each group. */
function bindChoiceGroup(root: HTMLElement, attribute: string, select: (value: string) => void) {
    const buttons = Array.from(root.querySelectorAll<HTMLButtonElement>(`[data-${attribute}]`));
    const showSelection = (value: string) => {
        for (const button of buttons) {
            const active = button.getAttribute(`data-${attribute}`) === value;
            button.classList.toggle('active', active);
            button.setAttribute('aria-pressed', String(active));
        }
    };
    for (const button of buttons) {
        button.setAttribute('aria-pressed', String(button.classList.contains('active')));
        button.onclick = () => {
            const value = button.getAttribute(`data-${attribute}`)!;
            showSelection(value);
            select(value);
        };
    }
    return showSelection;
}

/** Bind once to the workspace shell, using the canvas symbol geometry in its menu. */
export function createWorkspaceControls(actions: ControlActions) {
    const tools = element('tools');
    for (const kind of ['pin', 'roller', 'fixed', 'guided']) {
        tools.querySelector(`[data-tool="${kind}"] span`)!.innerHTML =
            `<svg class="tool-icon" viewBox="-28 -4 56 44" aria-hidden="true"><g stroke="currentColor" stroke-width="2" fill="none">${supportShape(kind)}</g></svg>`;
    }
    const loadIcons: Record<string, string> = {
        force: forceSymbol(20, 35, 0, -1, 'currentColor', '', 30, 0),
        moment: momentSymbol(20, 20, 1, 'currentColor', '', 14),
        distributed: '<path d="M 5 5 H 35" fill="none" stroke="currentColor" stroke-width="1.8"/>'
            + [5, 15, 25, 35].map(x => forceSymbol(x, 35, 0, -1, 'currentColor', '', 30, 0)).join(''),
    };
    for (const [kind, shape] of Object.entries(loadIcons)) {
        tools.querySelector(`[data-tool="${kind}"] span`)!.innerHTML =
            `<svg class="tool-icon load-tool-icon" viewBox="0 0 40 40" aria-hidden="true">${shape}</svg>`;
    }

    bindChoiceGroup(tools, 'tool', tool => {
        const hints: Record<string, string> = {
            select: 'Select an object to edit. Drag to move.',
            member: 'Click the start and end points. Snap to a member to create a rigid joint.',
            distributed: 'Click the start and end of the loaded interval on one member.',
            delete: 'Click an object to delete it. Undo restores the previous model.',
        };
        element('tool-hint').textContent = hints[tool]
            || 'Click a member to place this object. Select it to edit its properties.';
        actions.selectTool(tool);
    });
    const showLayer = bindChoiceGroup(element('layers'), 'layer', actions.selectLayer);
    const showMode = bindChoiceGroup(document.querySelector('nav')!, 'mode', actions.selectMode);

    return {
        showMode,
        showLayer,
        setHistory(canUndo: boolean, canRedo: boolean): void {
            element<HTMLButtonElement>('undo').disabled = !canUndo;
            element<HTMLButtonElement>('redo').disabled = !canRedo;
        },
        /** Hide panels without changing the model, view scale, or drawing tool. */
        setFocus(focused: boolean): void {
            document.querySelector('.work-grid')!.classList.toggle('is-focused', focused);
            const button = element('focus-workspace');
            button.setAttribute('aria-pressed', String(focused));
            button.textContent = focused ? 'Show side panels' : 'Focus view';
            button.title = focused ? 'Restore drawing tools and object properties (Esc)'
                : 'Hide side panels and enlarge the drawing';
        },
    };
}
