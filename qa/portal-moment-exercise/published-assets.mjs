/** Verify the published bytes against the reviewed Git worktree before and
 * after exercising the public site in a fresh, offline-recording browser. */
import assert from 'node:assert/strict';
import { createHash, randomUUID } from 'node:crypto';
import { readFile, mkdir, writeFile } from 'node:fs/promises';
import { setTimeout as delay } from 'node:timers/promises';

const [base, expectedCommit, output, phase] = process.argv.slice(2);
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
async function published(path) {
    const url = new URL(path, base);
    url.searchParams.set('verify', randomUUID());
    const response = await fetch(url, { cache: 'no-store', signal: AbortSignal.timeout(45000) });
    assert.equal(response.status, 200, url.href);
    return { url: url.href, bytes: Buffer.from(await response.arrayBuffer()) };
}
await mkdir(output, {recursive:true});
const deadline = Date.now() + (phase === 'before' ? 35*60*1000 : 0);
let metadata;
do {
    metadata = await published('verification.json');
    const live = JSON.parse(metadata.bytes);
    if (live.commit === expectedCommit) break;
    console.log('Published revision', live.commit);
    assert.ok(Date.now() < deadline, 'Reviewed revision is not live');
    await delay(30000);
} while (true);
const files = {};
for (const bundle of ['bundle','diagram','inclined-diagram']) {
    for (const name of ['manifest.json','checker.wasm','worker.mjs']) {
        const path = 'portal-checker/' + bundle + '/' + name;
        const remote = await published(path);
        const digest = hash(remote.bytes);
        assert.equal(digest, hash(await readFile('public/'+path)), path);
        files[path] = {sha256:digest, bytes:remote.bytes.length};
    }
}
await writeFile(output+'/deployment-'+phase+'.json',JSON.stringify({
    checkedAt:new Date().toISOString(), verification:JSON.parse(metadata.bytes),
    verificationUrl:metadata.url, verificationSha256:hash(metadata.bytes), files
},null,2));
console.log('Verified published revision and checker assets',expectedCommit,phase);
