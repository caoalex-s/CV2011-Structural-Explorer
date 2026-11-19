import { readFile, writeFile, readdir, copyFile } from 'node:fs/promises';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { stripTypeScriptTypes } from 'node:module';

const directory = '.data/hinge-build/spring-assets';
for (const name of ['engine', 'model-evidence', 'frame-rational', 'frame-candidate', 'frame-worker-bytes',
    'frame-interval', 'frame-interval-geometry', 'frame-interval-basis', 'frame-interval-solve', 'frame-interval-model',
    'frame-interval-abi', 'frame-inclined-release', 'frame-spring-packet']) {
    const source = await readFile('web/' + name + '.ts', 'utf8');
    await writeFile(join(directory, name + '.js'), stripTypeScriptTypes(source));
}
await copyFile('qa/frame-spring/worker.mjs', join(directory, 'worker.mjs'));
const files = {};
for (const name of (await readdir(directory)).sort()) {
    files[name] = createHash('sha256').update(await readFile(join(directory, name))).digest('hex');
}
await writeFile(join(directory, 'manifest.json'), JSON.stringify({ files }, null, 2));
