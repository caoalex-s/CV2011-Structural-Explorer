// Build a static Pages artifact without copying server code or student records.
import { mkdir, readdir, readFile, writeFile, copyFile, cp } from 'node:fs/promises';
import { stripTypeScriptTypes } from 'node:module';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { currentRealBeamReceipt, proofBundleHash } from './proof-bundle.mjs';

// Build lessons first, then supply the workspace, fonts, and proof receipts.
const lessons = spawnSync(process.execPath, ['node_modules/astro/bin/astro.mjs', 'build'], {
  stdio: 'inherit', env: { ...process.env, ASTRO_TELEMETRY_DISABLED: '1' },
});
if (lessons.status !== 0) throw new Error('The lesson build failed.', { cause: lessons.error });
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
// A new layout must not reuse an older cached stylesheet. The content hash
// changes only when that stylesheet changes, preserving ordinary caching.
let indexHtml = await readFile('dist/index.html', 'utf8');
for (const name of ['theme.css', 'style.css', 'worked.css', 'workspace.css']) {
  const stylesheet = await readFile(`dist/${name}`);
  const revision = createHash('sha256').update(stylesheet).digest('hex').slice(0, 12);
  indexHtml = indexHtml.replace(`href="${name}"`, `href="${name}?v=${revision}"`);
}
await writeFile('dist/index.html', indexHtml);
// Serve the pinned renderer and fonts from the same origin, including offline
// local use. The import map resolves the browser's bare `katex` import here.
const renderer = 'dist/vendor/katex';
await mkdir(renderer, { recursive: true });
for (const filename of ['katex.mjs', 'katex.min.css']) {
  await copyFile(`node_modules/katex/dist/${filename}`, `${renderer}/${filename}`);
}
await cp('node_modules/katex/dist/fonts', `${renderer}/fonts`, { recursive: true });
await cp('proofs/StructuralProofs.lean', 'dist/StructuralProofs.lean');
await copyFile('node_modules/katex/LICENSE', `${renderer}/LICENSE`);
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
// A checked generic receipt covers every local Lean source and the pinned
// dependency manifest. A stale or incomplete bundle never retains its badge.
const verificationPath = 'dist/verification.json';
const verification = JSON.parse(await readFile(verificationPath, 'utf8'));
if (verification.realBeam?.status === 'checked') {
  try {
    if (!currentRealBeamReceipt(verification.realBeam, await proofBundleHash())) verification.realBeam.status = 'pending';
  } catch {
    verification.realBeam.status = 'pending';
  }
  await writeFile(verificationPath, JSON.stringify(verification));
}
await import('./check_lessons.mjs');
console.log('Built static application in dist/');
