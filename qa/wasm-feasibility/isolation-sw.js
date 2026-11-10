/* Synthetic subpath diagnostic only. Derived from coi-serviceworker (MIT).
 * Upstream revision and full license are retained in hosting-source.json and
 * coi-LICENSE. This derivative has no page bootstrap, update timer, cache,
 * message handler, credential fallback or automatic navigation.
 */
self.addEventListener('install', event => event.waitUntil(self.skipWaiting()));
self.addEventListener('activate', event => event.waitUntil(self.clients.claim()));
self.addEventListener('fetch', event => {
    const request = event.request;
    const target = new URL(request.url);
    const scope = new URL(self.registration.scope);
    // Controlling a page must not rewrite its requests outside this test tree.
    if (target.origin !== scope.origin || !target.pathname.startsWith(scope.pathname)) return;
    if (request.cache === 'only-if-cached' && request.mode !== 'same-origin') return;
    event.respondWith(fetch(request).then(response => {
        if (response.status === 0) return response;
        const headers = new Headers(response.headers);
        headers.set('Cross-Origin-Opener-Policy', 'same-origin');
        headers.set('Cross-Origin-Embedder-Policy', 'require-corp');
        headers.set('Cross-Origin-Resource-Policy', 'same-origin');
        return new Response(response.body, {
            status: response.status, statusText: response.statusText, headers,
        });
    }));
});
