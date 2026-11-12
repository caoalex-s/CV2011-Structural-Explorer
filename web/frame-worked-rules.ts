/** Shared symbolic rules for explanatory records and their display. */
export const symbols: Record<string, string> = { x: 'x', L: '\\ell', c: 'c', s: 's', EA: 'EA', EI: 'EI',
    p: 'p', q: 'q', a1: 'a_1', a2: 'a_2', a3: 'a_3', u0: 'u_0', v0: 'v_0', theta0: '\\theta_0' };
type Operand = (key: string) => string;
// A single rule definition supplies symbolic and substituted forms. These
// are explanations, not a separate symbolic proof or emitted equality checker.
function localFields(v: Operand) {
    const x = v('x'), a1 = v('a1'), a2 = v('a2'), a3 = v('a3');
    return {
        N: `-${a1}-${v('p')}${x}`,
        V: `${a2}+${v('q')}${x}`,
        M: `-${a3}+${a2}${x}+\\frac{${v('q')}${x}^{2}}{2}`,
        rotation: `${v('theta0')}+\\frac{-${a3}${x}+${a2}${x}^{2}/2+${v('q')}${x}^{3}/6}{${v('EI')}}`,
        u: `${v('u0')}+\\frac{-${a1}${x}-${v('p')}${x}^{2}/2}{${v('EA')}}`,
        v: `${v('v0')}+${v('theta0')}${x}+\\frac{-${a3}${x}^{2}/2+${a2}${x}^{3}/6+${v('q')}${x}^{4}/24}{${v('EI')}}`,
    };
}
export function expression(id: string, v: Operand): string {
    const local = localFields(v);
    if (id === 'ux') return `${v('c')}\\left(${local.u}\\right)-${v('s')}\\left(${local.v}\\right)`;
    if (id === 'uy') return `${v('s')}\\left(${local.u}\\right)+${v('c')}\\left(${local.v}\\right)`;
    return local[id as keyof typeof local];
}
