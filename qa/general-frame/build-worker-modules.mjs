/** Reproduce the worker's five runtime modules using the workspace build's
 * type stripping. Called once inside each clean Linux artifact build.
 */
import { readFile, writeFile } from 'node:fs/promises';
import { stripTypeScriptTypes } from 'node:module';
import { resolve } from 'node:path';
const destination = process.argv[2];
if (!destination) throw Error('Supply the existing artifact asset directory.');
for (const name of ['frame-rational', 'model-evidence', 'frame-candidate', 'frame-packet', 'frame-result']) {
    const source = await readFile(resolve('web', name + '.ts'), 'utf8');
    await writeFile(resolve(destination, name + '.js'), stripTypeScriptTypes(source));
}
