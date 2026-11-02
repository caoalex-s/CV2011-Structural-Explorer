// Build a static Pages artifact without copying server code or student records.
import { mkdir, readdir, readFile, writeFile, copyFile } from 'node:fs/promises';
import { stripTypeScriptTypes } from 'node:module';
import { createHash } from 'node:crypto';
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
// Reuse a CI proof receipt locally only while the exact proof source is intact.
try {
  const receipt = JSON.parse(await readFile('proofs/verification-receipt.json', 'utf8'));
  const proof = await readFile('proofs/StructuralProofs.lean');
  const sourceHash = createHash('sha256').update(proof).digest('hex');
  const metadata = JSON.parse(await readFile('dist/verification.json', 'utf8'));
  if (sourceHash === receipt.source_sha256 && metadata.lean !== 'checked') {
    await writeFile('dist/verification.json', JSON.stringify({ ...metadata, ...receipt }));
  }
} catch {
  // A missing receipt leaves the explicitly pending source status unchanged.
}
console.log('Built static application in dist/');
