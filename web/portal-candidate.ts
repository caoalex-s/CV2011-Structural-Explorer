/** Untrusted exact candidate construction. Acceptance comes only from compiled Lean. */
import { example } from './engine.js';
import { parseEvidenceModel } from './model-evidence.js';
import { exactBinary64 } from './exact-cut-adapter.js';

export type Rational = { numerator: string; denominator: string };
export const portalQuery = Object.freeze({ member: 'BC', parameter: 0.5, cutSide: 'left' as const,
    quantity: 'M,uy', units: 'kN m,m', signConvention: 'sagging M positive; global y upward' });
export const coordinateIds = ['Ax', 'Ay', 'Arotation', 'Bx', 'By', 'Brotation', 'Cx', 'Cy', 'Crotation', 'Dx', 'Dy', 'Drotation'];
export const outputIds = [...coordinateIds, 'A:Fx', 'A:Fy', 'A:Mz', 'D:Fx', 'D:Fy', 'D:Mz', 'BC:midpoint:M', 'BC:midpoint:uy'];
export const profileId = 'shipped-portal-uniform-vertical/v1';
export const maxDigits = 128;

function canonical(value: unknown): string {
    if (Array.isArray(value)) return `[${value.map(canonical).join(',')}]`;
    if (value && typeof value === 'object') return `{${Object.entries(value).sort(([a], [b]) => a.localeCompare(b)).map(([key, child]) => `${JSON.stringify(key)}:${canonical(child)}`).join(',')}}`;
    return JSON.stringify(value);
}
function profile(input: unknown) {
    const model = parseEvidenceModel(input);
    return { ...model, loads: model.loads.map(({ label: _label, ...load }) => ({ ...load, fy: 0, qEnd: 0 })) };
}
const expectedProfile = canonical(profile(example('frame')));

/** Full normalized structure comparison. A digest or floating stability flag is insufficient. */
export function portalAmplitude(input: unknown): number {
    const model = parseEvidenceModel(input);
    if (model.loads.length !== 1 || canonical(profile(model)) !== expectedProfile || model.loads[0].fy !== model.loads[0].qEnd) {
        throw new Error('Unsupported model: keep the original portal and change only its uniform BC load.');
    }
    return model.loads[0].fy;
}

function rational(numerator: bigint, denominator: bigint): Rational {
    let a = numerator < 0n ? -numerator : numerator, b = denominator;
    while (b) [a, b] = [b, a % b];
    return { numerator: (numerator / a).toString(), denominator: (denominator / a).toString() };
}
function scale(value: Rational, numerator: bigint, denominator = 1n): Rational {
    return rational(BigInt(value.numerator) * numerator, BigInt(value.denominator) * denominator);
}

/** Unit response is an untrusted candidate only; Lean checks all equilibrium and recovery equations. */
export function portalCandidate(amplitude: number): Rational[] {
    const a = exactBinary64(amplitude);
    const unit: [bigint, bigint][] = [
        [0n, 1n], [0n, 1n], [0n, 1n], [-81n, 64157500n], [3n, 500000n], [14481n, 128315000n],
        [81n, 64157500n], [3n, 500000n], [-14481n, 128315000n], [0n, 1n], [0n, 1n], [0n, 1n],
        [-21600n, 25663n], [-3n, 1n], [28719n, 25663n], [21600n, 25663n], [-3n, 1n], [-28719n, 25663n],
        [-115605n, 51326n], [35315637n, 102652000000n],
    ];
    return [a, ...unit.map(([n, d]) => scale(a, n, d))];
}

/** Canonical bounded ASCII, shared with the C ABI. No conversion to Number. */
export function encodeCandidate(values: Rational[]): Uint8Array {
    if (values.length !== 21) throw new Error('Malformed certificate dimension');
    const fields = values.flatMap(({ numerator, denominator }) => {
        if (!/^(0|-?[1-9][0-9]*)$/.test(numerator) || !/^[1-9][0-9]*$/.test(denominator)) throw new Error('Malformed rational');
        if (numerator.replace('-', '').length > maxDigits || denominator.length > maxDigits) throw new Error('Limit exceeded: rational fields allow at most 128 decimal digits.');
        return [numerator, denominator];
    });
    return new TextEncoder().encode(fields.join('\n'));
}

/** Decimal rendering by integer division, rounded half away from zero. */
export function roundedDecimal(value: Rational, places: number, unitScale = 1n): string {
    const n = BigInt(value.numerator) * unitScale, d = BigInt(value.denominator);
    const sign = n < 0n ? '-' : '', magnitude = n < 0n ? -n : n;
    const factor = 10n ** BigInt(places);
    const rounded = (magnitude * factor * 2n + d) / (2n * d);
    const digits = rounded.toString().padStart(places + 1, '0');
    return `${rounded === 0n ? '' : sign}${places ? digits.slice(0, -places) + '.' + digits.slice(-places) : digits}`;
}
