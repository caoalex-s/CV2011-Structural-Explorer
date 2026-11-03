// Validate the exact public payload through the same notation and math renderer.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { resolveLoadNotation } from '../web/load-labels.ts';
import { equationHtml, math } from '../web/math.ts';

const library = JSON.parse(await readFile('web/worked-examples.json', 'utf8'));
let equations = 0;
let symbolicEquations = 0;
function check(value) {
    if (Array.isArray(value)) return value.forEach(check);
    if (value === null || typeof value !== 'object') return;
    if (typeof value.labelLatex === 'string' && typeof value.latex === 'string') {
        assert.doesNotMatch(equationHtml(value), /math-error|loadsymbol|loadname/);
        equations++;
        if (value.symbolicLatex !== undefined) symbolicEquations++;
    }
    for (const [key, child] of Object.entries(value)) {
        if (key.endsWith('Latex') && typeof child === 'string') {
            assert.doesNotMatch(math(child), /math-error|loadsymbol|loadname/);
        } else check(child);
    }
}
for (const example of library.examples) {
    for (const solution of example.solutions) {
        const response = resolveLoadNotation(solution.response, example.model);
        assert.equal(response.proof.status, 'checked');
        assert.equal(createHash('sha256').update(response.proof.source).digest('hex'), response.proof.sha256);
        check(response);
    }
}
assert.ok(symbolicEquations > 0, 'The public solutions must contain symbolic derivations.');
console.log(`Rendered ${equations} equations, including ${symbolicEquations} symbolic forms; all certificate hashes agree.`);
