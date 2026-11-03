/** Load names are presentation metadata; directions and components stay physical. */
import type { Load, Model } from './engine.js';

const prefixes = { force: 'P', moment: 'M', distributed: 'w' };

export function validLoadLabel(label: string, kind: Load['kind']): boolean {
    const base = kind === 'force' ? '[PF]' : kind === 'moment' ? 'M' : '[wq]';
    return new RegExp(`^${base}(?:_[A-Za-z0-9]{1,8})?$`).test(label);
}

/** Preserve existing names and give each unnamed action a distinct course symbol. */
export function loadLabels(model: Model): Map<string, string> {
    const labels = new Map<string, string>();
    const used = new Set(model.loads.map(load => load.label).filter((label): label is string => !!label));
    for (const load of model.loads) {
        if (load.label && validLoadLabel(load.label, load.kind) && ![...labels.values()].includes(load.label)) {
            labels.set(load.id, load.label);
            continue;
        }
        let index = load.kind === 'moment' ? 0 : 1;
        while (used.has(`${prefixes[load.kind]}_${index}`)) index++;
        const label = `${prefixes[load.kind]}_${index}`;
        used.add(label);
        labels.set(load.id, label);
    }
    return labels;
}

export function assignLoadLabels(model: Model): void {
    const labels = loadLabels(model);
    for (const load of model.loads) load.label = labels.get(load.id)!;
}

export function loadLabelLatex(label: string, component = ''): string {
    const [base, index = ''] = label.split('_');
    const subscript = [index, component].filter(Boolean).join(',');
    return subscript ? `${base}_{${subscript}}` : base;
}

export function loadLabelText(label: string): string {
    const digits = '₀₁₂₃₄₅₆₇₈₉';
    return label.replace(/_(\d+)$/, (_, index: string) => [...index].map(digit => digits[Number(digit)]).join(''));
}

/** Resolve generated notation tokens at display time. Renaming an action can
 * therefore reuse the same checked public model without stale equation labels. */
export function resolveLoadNotation<T>(value: T, model: Model): T {
    const labels = loadLabels(model);
    function resolve(item: unknown): unknown {
        if (typeof item === 'string') return item.replace(/\\loadsymbol\{(\d+)\}\{([xyab]?)\}/g,
            (_, index: string, component: string) => loadLabelLatex(labels.get(model.loads[Number(index)]?.id) || 'P', component))
            .replace(/\\loadname\{(\d+)\}/g, (_, index: string) => loadLabelText(labels.get(model.loads[Number(index)]?.id) || 'P'));
        if (Array.isArray(item)) return item.map(resolve);
        if (item !== null && typeof item === 'object') return Object.fromEntries(Object.entries(item).map(([key, child]) => [key, resolve(child)]));
        return item;
    }
    return resolve(value) as T;
}
