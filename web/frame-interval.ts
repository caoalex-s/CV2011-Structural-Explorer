/** Untrusted outward-rounded rational enclosures. Only the compiled checker may
 * establish containment in the original real model; this producer grants no status. */
import { type Fraction, fraction, zero, one, add, sub, mul, div, neg, compare } from './frame-rational.js';

export interface RationalInterval { lower: Fraction; upper: Fraction }

function floorRatio(numerator: bigint, denominator: bigint): bigint {
    const quotient = numerator / denominator;
    return numerator < 0n && numerator % denominator !== 0n ? quotient - 1n : quotient;
}

/** Integer square root, with no floating conversion or approximate stopping test. */
function integerSquareRoot(value: bigint): bigint {
    if (value < 0n) throw Error('Malformed square root: negative radicand.');
    if (value < 2n) return value;
    let upper = 1n << BigInt(Math.ceil(value.toString(2).length / 2));
    for (let iteration = 0; iteration < 512; iteration++) {
        const next = (upper + value / upper) / 2n;
        if (next >= upper) return upper;
        upper = next;
    }
    throw Error('Limit: integer square-root iteration budget exhausted.');
}

/** One context owns precision and an operation budget for a single attempt. */
export class IntervalArithmetic {
    readonly scale: bigint;
    readonly bits: number;
    private remaining: number;
    constructor(bits: number, operations = 2000000) {
        if (![32, 64, 96, 128].includes(bits)) throw Error('Malformed enclosure precision.');
        if (!Number.isSafeInteger(operations) || operations < 1 || operations > 2000000)
            throw Error('Malformed enclosure operation budget.');
        this.scale = 1n << BigInt(bits);
        this.bits = bits;
        this.remaining = operations;
    }

    private spend(): void {
        if (--this.remaining < 0) throw Error('Limit: enclosure operation budget exhausted.');
    }

    /** Round lower toward minus infinity and upper toward plus infinity. */
    bounds(lower: Fraction, upper = lower): RationalInterval {
        this.spend();
        if (compare(lower, upper) > 0) throw Error('Malformed interval: reversed bounds.');
        const low = floorRatio(lower.n * this.scale, lower.d);
        const high = -floorRatio(-upper.n * this.scale, upper.d);
        return { lower: fraction(low, this.scale), upper: fraction(high, this.scale) };
    }

    add(a: RationalInterval, b: RationalInterval): RationalInterval {
        return this.bounds(add(a.lower, b.lower), add(a.upper, b.upper));
    }

    subtract(a: RationalInterval, b: RationalInterval): RationalInterval {
        return this.bounds(sub(a.lower, b.upper), sub(a.upper, b.lower));
    }

    negate(a: RationalInterval): RationalInterval {
        return this.bounds(neg(a.upper), neg(a.lower));
    }

    multiply(a: RationalInterval, b: RationalInterval): RationalInterval {
        const products = [mul(a.lower, b.lower), mul(a.lower, b.upper), mul(a.upper, b.lower), mul(a.upper, b.upper)];
        products.sort(compare);
        return this.bounds(products[0], products[3]);
    }

    divide(a: RationalInterval, b: RationalInterval): RationalInterval {
        if (compare(b.lower, zero) <= 0 && compare(b.upper, zero) >= 0)
            throw Error('Inconclusive: denominator enclosure contains zero.');
        return this.multiply(a, this.bounds(div(one, b.upper), div(one, b.lower)));
    }

    squareRoot(a: RationalInterval): RationalInterval {
        if (compare(a.lower, zero) < 0) throw Error('Inconclusive: square-root enclosure extends below zero.');
        const scaledFloor = (value: Fraction) => integerSquareRoot(value.n * this.scale * this.scale / value.d);
        const low = scaledFloor(a.lower), highFloor = scaledFloor(a.upper);
        const exactUpper = highFloor * highFloor * a.upper.d === a.upper.n * this.scale * this.scale;
        return this.bounds(fraction(low, this.scale), fraction(highFloor + (exactUpper ? 0n : 1n), this.scale));
    }
}
