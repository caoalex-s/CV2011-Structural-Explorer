/** Pure mocked service-worker checks; no browser or WASM instantiation. */
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import vm from 'node:vm';
import test from 'node:test';

const source = await readFile(new URL('./isolation-sw.js', import.meta.url), 'utf8');
const scope = 'https://example.test/project/synthetic/';
function fixture() {
    const listeners = new Map();
    const fetched = [];
    const self = { registration: { scope }, skipWaiting: async () => {},
        clients: { claim: async () => {} }, addEventListener: (type, fn) => listeners.set(type, fn) };
    vm.runInNewContext(source, { self, URL, Headers, Response,
        fetch: async request => {
            fetched.push(request.url);
            return new Response('unchanged bytes', { status: 200, headers: { 'X-Original': 'retained' } });
        } });
    return { listeners, fetched };
}

test('only explicit install, activate and fetch listeners exist', () => {
    assert.deepEqual([...fixture().listeners.keys()], ['install', 'activate', 'fetch']);
});
test('same-origin in-scope response preserves bytes and adds isolation headers', async () => {
    const { listeners, fetched } = fixture();
    let pending;
    listeners.get('fetch')({ request: { url: scope + 'checker.wasm', mode: 'same-origin' },
        respondWith: promise => { pending = promise; } });
    const response = await pending;
    assert.equal(await response.text(), 'unchanged bytes');
    assert.equal(response.headers.get('X-Original'), 'retained');
    assert.equal(response.headers.get('Cross-Origin-Opener-Policy'), 'same-origin');
    assert.equal(response.headers.get('Cross-Origin-Embedder-Policy'), 'require-corp');
    assert.deepEqual(fetched, [scope + 'checker.wasm']);
});
test('neighbor paths, prefix collisions, external origins and invalid cache modes are untouched', () => {
    const { listeners, fetched } = fixture();
    for (const request of [{ url: 'https://example.test/project/outside.html' },
        { url: 'https://example.test/project/synthetic-other/asset' },
        { url: 'https://external.test/project/synthetic/asset' },
        { url: scope + 'asset', cache: 'only-if-cached', mode: 'no-cors' }]) {
        listeners.get('fetch')({ request, respondWith: () => assert.fail('Out-of-scope interception') });
    }
    assert.deepEqual(fetched, []);
});
