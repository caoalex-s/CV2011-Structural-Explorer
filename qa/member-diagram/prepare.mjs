import { copyFile, readdir, readFile, writeFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
const folder = '.data/hinge-build/diagram-assets/';
await copyFile('qa/member-diagram/worker.mjs', folder + 'worker.mjs');
const files = {};
for (const name of (await readdir(folder)).sort()) {
    files[name] = createHash('sha256').update(await readFile(folder + name)).digest('hex');
}
await writeFile(folder + 'manifest.json', JSON.stringify({ files }, null, 2));
