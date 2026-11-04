/** CI calls this only after building and auditing all real-beam theorems. */
import { readFile, writeFile } from 'node:fs/promises';
import { proofBundleHash } from './proof-bundle.mjs';

const filename = 'web/verification.json';
const verification = JSON.parse(await readFile(filename, 'utf8'));
verification.realBeam = { status: 'checked', theoremSet: 'point-force-real-fields-v1', sourceSha256: await proofBundleHash(),
    scope: 'Real polynomial calculus, point-action jumps, and the stated endpoint-supported point-force fields.' };
await writeFile(filename, JSON.stringify(verification) + '\n');
