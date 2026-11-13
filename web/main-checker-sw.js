/* Opt-in isolation for the repository's main workspace. Registration covers
 * this repository (including Learn); only the exact main document and named
 * checker resources below receive headers. There is no caching or data channel.
 */
self.addEventListener('install', event => event.waitUntil(self.skipWaiting()));
self.addEventListener('activate', event => event.waitUntil(self.clients.claim()));
const runtimeFiles = new Set(['worker.mjs', 'manifest.json', 'checker.wasm',
    'checker.mjs', 'checker.worker.js', 'checker.mjs.symbols', 'frame-rational.js',
    'model-evidence.js', 'frame-candidate.js', 'frame-packet.js', 'frame-result.js']);
self.addEventListener('fetch', event => {
    const request = event.request;
    const target = new URL(request.url);
    const scope = new URL(self.registration.scope);
    if (target.origin !== scope.origin || request.method !== 'GET') return;
    const mainDocument = request.mode === 'navigate' && request.destination === 'document' &&
        [scope.pathname, scope.pathname + 'index.html'].includes(target.pathname);
    const bundle = scope.pathname + 'portal-checker/bundle/';
    const checkerResource = target.pathname.startsWith(bundle) && runtimeFiles.has(target.pathname.slice(bundle.length));
    if (!mainDocument && !checkerResource) return;
    if (request.cache === 'only-if-cached' && request.mode !== 'same-origin') return;
    event.respondWith(fetch(request).then(response => {
        if (!response.ok || response.type === 'opaque') return response;
        const headers = new Headers(response.headers);
        headers.set('Cross-Origin-Opener-Policy', 'same-origin');
        headers.set('Cross-Origin-Embedder-Policy', 'require-corp');
        headers.set('Cross-Origin-Resource-Policy', 'same-origin');
        return new Response(response.body, { status: response.status, statusText: response.statusText, headers });
    }));
});
