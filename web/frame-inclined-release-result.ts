/** Decode exact report bytes only after compiled checker acceptance.
 * This parser validates representation and identities; it grants no checked status.
 * Decimal rendering must remain separate from these exact rational values.
 */
import { fraction, type Fraction, encoded } from './frame-rational.js';

import type { IntervalPoint, IntervalReadout } from './frame-interval-result.js';

export function decodeInclinedReleaseReport(bytes: Uint8Array) {
    if (bytes.length > 262144) throw Error('Interval report exceeds its byte budget.');
    // Check original bytes: TextDecoder otherwise silently strips a UTF-8 BOM.
    for (const byte of bytes)
        if (byte !== 10 && (byte < 32 || byte > 126)) throw Error('Invalid interval report characters.');
    const text = new TextDecoder('utf-8', { fatal: true }).decode(bytes);
    let lines = 1;
    for (const character of text) if (character === '\n') lines++;
    if (lines > 1024) throw Error('Too many interval report fields.');
    const tokens = text.split('\n');
    let position = 0;
    const token = (): string => {
        if (position >= tokens.length) throw Error('Truncated interval report.');
        return tokens[position++];
    };
    const natural = (maximum: number): number => {
        const value = token();
        if (!/^(0|[1-9]\d{0,2})$/.test(value) || Number(value) > maximum)
            throw Error('Invalid interval report index or count.');
        return Number(value);
    };
    const rational = (digits = 128): Fraction => {
        const numerator = token(), denominator = token();
        if (numerator.length > digits + 1 || denominator.length > digits ||
            !/^-?(0|[1-9]\d*)$/.test(numerator) || numerator === '-0' || !/^[1-9]\d*$/.test(denominator))
            throw Error('Invalid interval report rational.');
        const value = fraction(BigInt(numerator), BigInt(denominator), digits);
        if (String(value.n) !== numerator || String(value.d) !== denominator)
            throw Error('Noncanonical interval report rational.');
        return value;
    };
    const identifier = (): string => {
        const value = token();
        if (!/^(?:[0-9a-f]{4}){1,256}$/.test(value)) throw Error('Invalid interval report identifier.');
        let decoded = '';
        for (let index = 0; index < value.length; index += 4)
            decoded += String.fromCharCode(Number.parseInt(value.slice(index, index + 4), 16));
        return decoded;
    };
    const interval = (): IntervalReadout => {
        const lower = rational(), upper = rational();
        // A midpoint formed from two bounded fractions can need extra digits.
        const midpoint = rational(257);
        if (lower.n * upper.d > upper.n * lower.d) throw Error('Reversed interval report bounds.');
        if (2n * midpoint.n * lower.d * upper.d !== midpoint.d * (lower.n * upper.d + upper.n * lower.d))
            throw Error('Report midpoint differs from the accepted interval midpoint.');
        return { lower: encoded(lower), upper: encoded(upper), midpoint: encoded(midpoint) };
    };

    if (token() !== 'CV2011_RELEASE_RESULT_1') throw Error('Unsupported interval report version.');
    const member = identifier();
    const parameter = rational();
    if (parameter.n < 0n || parameter.n > parameter.d) throw Error('Invalid interval report query parameter.');
    const cutSide: 'left' | 'right' = natural(1) === 1 ? 'right' : 'left';
    if (natural(1) !== 1) throw Error('Unsupported interval report convention.');
    const pointCount = natural(16);
    if (!pointCount) throw Error('Empty interval report point map.');
    const fields = Array.from({ length: 6 }, interval);
    const points: IntervalPoint[] = [];
    for (let point = 0; point < pointCount; point++) {
        const owner = natural(1) === 1 ? 'member' : 'node';
        const index = natural(owner === 'node' ? 15 : 7);
        const id = identifier();
        const parameter = rational();
        if (owner === 'node' ? parameter.n !== 0n : parameter.n <= 0n || parameter.n >= parameter.d)
            throw Error('Invalid interval report point ownership parameter.');
        points.push({ owner, index, id, parameter: encoded(parameter), reactions: Array.from({ length: 3 }, interval) });
    }
    const count = natural(16);
    const faces = Array.from({ length: count }, () => ({
        node: identifier(), member: identifier(), end: natural(1), released: natural(1) === 1,
        ux: interval(), uy: interval(), rotation: interval(), moment: interval(),
    }));
    if (position !== tokens.length) throw Error('Unexpected trailing interval report fields.');
    return { query: { member, parameter: encoded(parameter), cutSide, convention: 1 as const }, fields, points, faces };
}
