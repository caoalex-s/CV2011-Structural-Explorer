/** Bounded exact arithmetic for the untrusted frame candidate producer.
 * This module never grants acceptance. The compiled checker independently
 * derives the model and checks the proposed certificate.
 */
export type Fraction = { n: bigint; d: bigint };
export const zero: Fraction = Object.freeze({ n: 0n, d: 1n });
export const one: Fraction = Object.freeze({ n: 1n, d: 1n });
export const maxRationalDigits = 128;

function gcd(a: bigint, b: bigint): bigint {
    while (b !== 0n) [a, b] = [b, a % b];
    return a;
}

/** Normalize after every operation; excessive growth is a resource limit. */
export function fraction(n: bigint, d = 1n): Fraction {
    if (d === 0n) throw Error('Malformed rational: zero denominator.');
    if (d < 0n) { n = -n; d = -d; }
    const divisor = gcd(n < 0n ? -n : n, d);
    const numerator = n / divisor, denominator = d / divisor;
    if ((numerator < 0n ? -numerator : numerator).toString().length > maxRationalDigits ||
        denominator.toString().length > maxRationalDigits) throw Error('Limit: rational arithmetic exceeds 128 digits.');
    return { n: numerator, d: denominator };
}
export const add = (a: Fraction, b: Fraction): Fraction => fraction(a.n * b.d + b.n * a.d, a.d * b.d);
export const neg = (a: Fraction): Fraction => ({ n: -a.n, d: a.d });
export const sub = (a: Fraction, b: Fraction): Fraction => add(a, neg(b));
export const mul = (a: Fraction, b: Fraction): Fraction => fraction(a.n * b.n, a.d * b.d);
export const div = (a: Fraction, b: Fraction): Fraction => fraction(a.n * b.d, a.d * b.n);
export const integer = (value: number): Fraction => fraction(BigInt(value));
export const equal = (a: Fraction, b: Fraction): boolean => a.n === b.n && a.d === b.d;
export const compare = (a: Fraction, b: Fraction): number => {
    const difference = a.n * b.d - b.n * a.d;
    return difference < 0n ? -1 : difference > 0n ? 1 : 0;
};
export const absolute = (a: Fraction): Fraction => a.n < 0n ? neg(a) : a;
export const square = (a: Fraction): Fraction => mul(a, a);
export const encoded = (a: Fraction) => ({ numerator: a.n.toString(), denominator: a.d.toString() });

/** The represented binary64 value, without decimal reconstruction or rounding. */
export function binary64(value: number): Fraction {
    if (!Number.isFinite(value)) throw Error('Malformed input: a finite number is required.');
    if (value === 0) return zero;
    const data = new DataView(new ArrayBuffer(8));
    data.setFloat64(0, value, false);
    const bits = data.getBigUint64(0, false);
    const negative = bits >> 63n !== 0n;
    const exponent = Number((bits >> 52n) & 2047n);
    const mantissa = bits & ((1n << 52n) - 1n);
    let numerator = exponent === 0 ? mantissa : mantissa + (1n << 52n);
    const power = exponent === 0 ? -1074 : exponent - 1023 - 52;
    if (negative) numerator = -numerator;
    return power >= 0 ? fraction(numerator << BigInt(power)) : fraction(numerator, 1n << BigInt(-power));
}

export function sum(values: Iterable<Fraction>): Fraction {
    let answer = zero;
    for (const value of values) answer = add(answer, value);
    return answer;
}
export const dot = (a: Fraction[], b: Fraction[]): Fraction => {
    if (a.length !== b.length) throw Error('Malformed candidate dimensions.');
    return sum(a.map((value, i) => mul(value, b[i])));
};
