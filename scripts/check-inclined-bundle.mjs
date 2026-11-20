/** Bind the installed Stage 1 bundle to accepted bytes and current source. */
import assert from 'node:assert/strict';
import { readFile, readdir } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { stripTypeScriptTypes } from 'node:module';
import { execFileSync } from 'node:child_process';

const directory = 'public/portal-checker/bundle/';
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const bytes = await readFile(directory + 'manifest.json');
assert.equal(hash(bytes), 'f886a80a23c441f63f64335e61614051c68b08d232c11778ea2606467702b9b0');
const manifest = JSON.parse(bytes);
assert.equal(manifest.sourceCommit, '038b0a48c95022647af26fd5dd6165abf5a92c8f');
assert.equal(manifest.theorem, 'InclinedFrameIntervalReportSound.checkReport_sound');
assert.deepEqual((await readdir(directory)).sort(), [...Object.keys(manifest.files), 'manifest.json', 'worker.mjs'].sort());
for (const [name, expected] of Object.entries(manifest.files)) {
    assert.equal(hash(await readFile(directory + name)), expected, name);
    if (name.endsWith('.js') && name !== 'checker.worker.js') {
        const source = await readFile('web/' + name.replace(/\.js$/, '.ts'), 'utf8');
        assert.equal(hash(stripTypeScriptTypes(source)), expected, 'Current TypeScript: ' + name);
    }
}
// Git blobs are the exact Linux build inputs. A Windows checkout may use CRLF;
// require no semantic/index changes and hash committed bytes without altering them.
execFileSync('git', ['diff', '--exit-code', 'HEAD', '--', 'proofs']);
for (const [name, expected] of Object.entries(manifest.proofFiles))
    assert.equal(hash(execFileSync('git', ['show', 'HEAD:proofs/' + name])), expected, 'Current proof: ' + name);
assert.equal(hash(await readFile(directory + 'worker.mjs')), manifest.workerSha256);
assert.equal(hash(await readFile('qa/inclined-frame/worker.mjs')), manifest.workerSha256);
assert.equal(hash(await readFile('qa/inclined-frame/abi.c')), manifest.abiSha256);
console.log('Accepted inclined bundle matches every installed asset, proof, ABI, worker and generated module.');
