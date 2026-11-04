/** Small presentation helpers shared by workspace components. */
export const element = <T extends HTMLElement = HTMLElement>(id: string) =>
    document.getElementById(id) as T;

export function escapeHtml(value: unknown): string {
    const entities: Record<string, string> = {
        '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
    };
    return String(value).replace(/[&<>"']/g, character => entities[character]);
}

/** Retain the established significant-digit display and numerical zero threshold. */
export function formatNumber(value: number, digits = 3): string {
    return Math.abs(value) < 1e-8 ? '0' : Number(value.toPrecision(digits)).toString();
}

export function downloadJson(name: string, data: unknown): void {
    const blob = new Blob([JSON.stringify(data, null, 2)], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const anchor = document.createElement('a');
    anchor.href = url;
    anchor.download = name;
    anchor.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
}
