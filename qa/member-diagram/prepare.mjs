import { copyFile, readdir, readFile, writeFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
const folder = '.data/hinge-build/diagram-assets/';
for (const module of ['frame-worker-bytes.js', 'frame-interval-abi.js']) {
    await copyFile('public/portal-checker/spring/' + module, folder + module);
}
await copyFile('qa/member-diagram/worker.mjs', folder + 'worker.mjs');
const files = {};
for (const name of (await readdir(folder)).sort()) {
    files[name] = createHash('sha256').update(await readFile(folder + name)).digest('hex');
}
await writeFile(folder + 'manifest.json', JSON.stringify({ files }, null, 2));
