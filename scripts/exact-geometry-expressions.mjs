/** A deliberately small, test-only translator from adapter expressions to Lean.
 * It never includes model IDs, labels, or arbitrary source fragments. */
const operations = {
    add: { arity: 2, emit: args => `(${args[0]} + ${args[1]})` },
    multiply: { arity: 2, emit: args => `(${args[0]} * ${args[1]})` },
    divide: { arity: 2, emit: args => `(${args[0]} / ${args[1]})` },
    square: { arity: 1, emit: args => `(${args[0]})^2` },
    sqrt: { arity: 1, emit: args => `Real.sqrt (${args[0]})` },
    sin: { arity: 1, emit: args => `Real.sin (${args[0]})` },
    cos: { arity: 1, emit: args => `Real.cos (${args[0]})` },
    pi: { arity: 0, emit: () => 'Real.pi' },
};

export function emitExactExpression(value) {
    if (!value || typeof value !== 'object' || Array.isArray(value)) throw Error('Expected expression object');
    if ('numerator' in value || 'denominator' in value) {
        if (Object.keys(value).length !== 2 || typeof value.numerator !== 'string' || typeof value.denominator !== 'string' ||
            !/^-?(0|[1-9][0-9]*)$/.test(value.numerator) || !/^[1-9][0-9]*$/.test(value.denominator))
            throw Error('Malformed exact rational');
        return `((${value.numerator} : ℝ) / ${value.denominator})`;
    }
    if (Object.keys(value).length !== 2 || typeof value.op !== 'string' || !Array.isArray(value.args) ||
        !Object.hasOwn(operations, value.op)) throw Error('Unknown expression');
    const operation = operations[value.op];
    if (value.args.length !== operation.arity) throw Error('Wrong expression arity');
    return operation.emit(value.args.map(emitExactExpression));
}
