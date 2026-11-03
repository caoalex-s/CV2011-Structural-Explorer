/** LaTeX rendering shared by computed equations and the course method rules. */
import katex from 'katex';

const escapeHtml = (text: string) => text.replace(/[&<>"']/g, character =>
    ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[character]!));

export interface Equation {
    label: string;
    labelLatex: string;
    latex: string;
    exact: string;
    unit: string;
}

export function math(source: string, display = false): string {
    try {
        return katex.renderToString(source, {
            displayMode: display,
            output: 'htmlAndMathml',
            throwOnError: true,
            strict: 'error',
            trust: false,
            maxExpand: 1000,
            maxSize: 20,
        });
    } catch {
        // Preserve the expression and make a rendering failure explicit.
        return `<code class="math-error" aria-label="Equation could not be typeset">${escapeHtml(source)}</code>`;
    }
}

export function rationalLatex(value: string): string {
    const fraction = /^(-?\d+)\/(\d+)$/.exec(value);
    return fraction ? `\\frac{${fraction[1]}}{${fraction[2]}}` : value;
}

export function equationHtml(row: Equation): string {
    const units: Record<string, string> = {
        'kN': String.raw`\mathrm{kN}`, 'kN m': String.raw`\mathrm{kN}\,\mathrm{m}`,
        'kN/m': String.raw`\mathrm{kN}/\mathrm{m}`, 'm': String.raw`\mathrm{m}`,
        'mm': String.raw`\mathrm{mm}`, 'rad': String.raw`\mathrm{rad}`,
    };
    const unit = units[row.unit];
    const source = `${row.labelLatex} = ${row.latex}${unit ? `\\;${unit}` : ''}`;
    return `<div class="worked-equation">${math(source, true)}</div>`;
}

/** Shared equations remain ordinary LaTeX that an instructor can edit. */
export const methodRules = {
    reactions: String.raw`\begin{aligned}
        \sum F_x &= 0, & R_{\mathrm l}+R_{\mathrm r}+F &= 0,\\
        \sum M_a &= R_{\mathrm r}(b-a)+T-aF=0.
        \end{aligned}`,
    sections: String.raw`\begin{aligned}
        N(x)&=-\sum_{x_i\le x}F_{x,i},\\
        V(x)&=\sum_{x_i\le x}F_{y,i}+\int_0^x q(s)\,\mathrm{d}s,\\
        M(x)&=\sum_{x_i\le x}F_{y,i}(x-x_i)-\sum_{x_i\le x}C_i
            +\int_0^x q(s)(x-s)\,\mathrm{d}s.
        \end{aligned}`,
    integration: String.raw`\begin{aligned}
        EI\,v''(x)&=M(x),\\
        \theta(x)=v'(x)&=\int\frac{M(x)}{EI}\,\mathrm{d}x+C_{1,i},\\
        v(x)&=\int\theta(x)\,\mathrm{d}x+C_{0,i}.
        \end{aligned}`,
    conditions: String.raw`\begin{aligned}
        v(a)&=v(b)=0,\\
        C_1&=-\frac{B(b)-B(a)}{b-a}, & C_0&=-B(a)-aC_1,\\
        v(x_i^-)&=v(x_i^+), & \theta(x_i^-)&=\theta(x_i^+).
        \end{aligned}`,
    area: String.raw`\begin{aligned}
        \theta(c)-\theta(a)&=\int_a^c\frac{M(x)}{EI}\,\mathrm{d}x,\\
        t_{c/a}&=\int_a^c(c-x)\frac{M(x)}{EI}\,\mathrm{d}x,\\
        v(c)&=v(a)+(c-a)\theta(a)+t_{c/a}.
        \end{aligned}`,
    virtual: String.raw`(1\,\mathrm{kN})\,v(x_s)=\sum_i\int_{x_{i,a}}^{x_{i,b}}\frac{m_i(x)M_i(x)}{EI}\,\mathrm{d}x.`,
};
