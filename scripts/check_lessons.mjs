// Check the actual static artifact, including deployment under a Pages subpath.
import assert from 'node:assert/strict';
import { readFile, stat } from 'node:fs/promises';

const base = process.env.EXPLORER_BASE || '/';
let references = 0;
for (const route of ['learn/', 'learn/beam-basics/']) {
    const html = await readFile(`dist/${route}index.html`, 'utf8');
    assert.ok(html.includes('<h1'), `${route}: missing heading`);
    assert.ok(!/class="(?:math-error|katex-error)/.test(html), `${route}: equation rendering error`);
    for (const match of html.matchAll(/(?:href|src)="([^"]+)"/g)) {
        const url = new URL(match[1].replaceAll('&amp;', '&'), `https://lesson.invalid${base}${route}`);
        if (url.origin !== 'https://lesson.invalid') continue;
        assert.ok(url.pathname.startsWith(base), `${route}: link escapes deployment base: ${url.pathname}`);
        const relative = decodeURIComponent(url.pathname.slice(base.length));
        const target = `dist/${relative}${relative.endsWith('/') || relative === '' ? 'index.html' : ''}`;
        assert.ok((await stat(target)).isFile(), `${route}: missing ${target}`);
        references++;
    }
}
console.log(`Checked both Learn routes and ${references} local links/assets at base ${base}`);
