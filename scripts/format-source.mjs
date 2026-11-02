// Expand the TypeScript source with the compiler printer for readable review.
import { readFile, writeFile } from 'node:fs/promises';
let typescript;
try {
  typescript = (await import('typescript')).default;
} catch {
  typescript = (await import('../.tools/typescript/package/lib/typescript.js')).default;
}
const printer = typescript.createPrinter({ newLine: typescript.NewLineKind.LineFeed });
for (const filename of ['web/engine.ts', 'web/app.ts']) {
  const source = await readFile(filename, 'utf8');
  const parsed = typescript.createSourceFile(filename, source, typescript.ScriptTarget.Latest, true);
  await writeFile(filename, printer.printFile(parsed));
}
