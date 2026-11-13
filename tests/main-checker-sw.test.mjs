import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { runInNewContext } from 'node:vm';

const source = await readFile(new URL('../web/main-checker-sw.js', import.meta.url), 'utf8');
const base = 'https://example.invalid/course/';
function fixture() {
    const handlers = new Map(), fetched = [];
    runInNewContext(source, { URL, Headers, Response,
        self: { registration: { scope: base }, addEventListener: (name, handler) => handlers.set(name, handler) },
        fetch: async request => { fetched.push(request.url); return new Response('public asset'); } });
    return { fetched, request: async (path, mode = 'navigate', destination = 'document', method = 'GET') => {
        let response;
        handlers.get('fetch')({ request: { url: new URL(path, base).href, mode, destination, method },
            respondWith: promise => { response = promise; } });
        return response ? await response : undefined;
    } };
}
test('root isolation changes only exact main navigation and named checker resources', async () => {
    const { request } = fixture();
    for (const path of ['', '?lesson=beam#practice', 'index.html?view=1']) {
        const response = await request(path);
        assert.equal(response.headers.get('Cross-Origin-Opener-Policy'), 'same-origin');
        assert.equal(response.headers.get('Cross-Origin-Embedder-Policy'), 'require-corp');
    }
    const worker = await request('portal-checker/bundle/worker.mjs', 'same-origin', 'worker');
    assert.equal(worker.headers.get('Cross-Origin-Embedder-Policy'), 'require-corp');
});
test('Learn, scoped documents, unknown resources and other origins pass through untouched', async () => {
    const { request, fetched } = fixture();
    for (const path of ['learn/', 'learn/beam-basics/', 'portal-checker/', 'checker-preview/',
        'unrelated.js', 'portal-checker/bundle/unlisted.js', 'portal-checker/bundle/nested/worker.mjs',
        '../', 'https://other.invalid/course/', '/course-other/']) assert.equal(await request(path), undefined);
    assert.equal(await request('', 'same-origin', 'empty'), undefined);
    assert.equal(await request('', 'navigate', 'document', 'POST'), undefined);
    assert.deepEqual(fetched, []);
});
