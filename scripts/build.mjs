// Build a static Pages artifact without copying server code or student records.
import { mkdir, readdir, readFile, writeFile, copyFile } from 'node:fs/promises';
import { stripTypeScriptTypes } from 'node:module';
await mkdir('dist', { recursive: true });
for (const name of await readdir('web')) {
  if (name.endsWith('.ts')) {
    const source = await readFile(`web/${name}`, 'utf8');
    await writeFile(`dist/${name.replace(/\.ts$/, '.js')}`, stripTypeScriptTypes(source));
  } else {
    await copyFile(`web/${name}`, `dist/${name}`);
  }
}
await writeFile('dist/.nojekyll', '');
console.log('Built static application in dist/');
