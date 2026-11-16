/** Prepare the unchanged exact-route modules plus inclined proposal/report code.
 * Type stripping is the workspace's existing reproducible build operation.
 * This prepares JavaScript only; it does not build or accept a checker artifact.
 */
import { readFile, writeFile } from 'node:fs/promises';
import { stripTypeScriptTypes } from 'node:module';
import { resolve } from 'node:path';
const destination = process.argv[2];
if (!destination) throw Error('Supply the existing artifact asset directory.');
await import('../general-frame/build-worker-modules.mjs');
for (const name of ['frame-interval', 'frame-interval-geometry', 'frame-interval-basis',
    'frame-interval-model', 'frame-interval-solve', 'frame-interval-packet', 'frame-interval-result']) {
    const source = await readFile(resolve('web', name + '.ts'), 'utf8');
    await writeFile(resolve(destination, name + '.js'), stripTypeScriptTypes(source));
}
