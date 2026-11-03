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
        'kN m²': String.raw`\mathrm{kN}\,\mathrm{m}^2`, 'kN m³': String.raw`\mathrm{kN}\,\mathrm{m}^3`,
    };
    const unit = units[row.unit];
    const source = `${row.labelLatex} = ${row.latex}${unit ? `\\;${unit}` : ''}`;
    return `<div class="worked-equation">${math(source, true)}</div>`;
}

/** Shared equations remain ordinary LaTeX that an instructor can edit. */
export const methodRules = {
    sections: String.raw`\begin{aligned}
        N(x)&=-\sum_{x_i\le x}F_{x,i},\\
        V(x)&=\sum_{x_i\le x}F_{y,i}-\int_0^x w(s)\,\mathrm{d}s,\\
        M(x)&=\sum_{x_i\le x}F_{y,i}(x-x_i)-\sum_{x_i\le x}C_i
            -\int_0^x w(s)(x-s)\,\mathrm{d}s.
        \end{aligned}`,
    integration: String.raw`\begin{aligned}
        EI\,v_i''(x)&=M_i(x),\\
        EI\,\theta_i(x)=EI\,v_i'(x)&=\int M_i(x)\,\mathrm{d}x+C_{2i-1},\\
        EI\,v_i(x)&=\int EI\,\theta_i(x)\,\mathrm{d}x+C_{2i}.
        \end{aligned}`,
    conditions: String.raw`\begin{aligned}
        v(a)&=v(b)=0,\\
        v(x_i^-)&=v(x_i^+), & \theta(x_i^-)&=\theta(x_i^+).
        \end{aligned}`,
    area: String.raw`\begin{aligned}
        \theta_Q-\theta_P&=\int_{x_P}^{x_Q}\frac{M(x)}{EI}\,\mathrm{d}x,\\
        t_{Q/P}&=\int_{x_P}^{x_Q}(x_Q-x)\frac{M(x)}{EI}\,\mathrm{d}x,\\
        v_Q&=v_P+(x_Q-x_P)\theta_P+t_{Q/P}.
        \end{aligned}`,
    virtual: String.raw`\begin{aligned}
        \bar P\Delta_{s\mathrm v}&=\sum_i\int\frac{\bar M_i M_i}{EI}\,\mathrm{d}x,&\bar M_i&=\bar Pm_i,\\
        \Delta_{s\mathrm v}&=\sum_i\int\frac{m_i M_i}{EI}\,\mathrm{d}x=-v(x_s).
        \end{aligned}`,
};
