/** Trusted course prose permits inline $LaTeX$; all non-math text is escaped. */
import { math } from './math.js';
import { escapeHtml } from './ui.js';

export function lessonText(source: string): string {
    return source.split(/(\$[^$]+\$)/g).map(part =>
        part.startsWith('$') && part.endsWith('$') ? math(part.slice(1, -1)) : escapeHtml(part),
    ).join('');
}
