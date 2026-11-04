import { defineConfig } from 'astro/config';

// Astro owns the static Learn routes. The existing build adds the workspace
// after Astro has cleared dist/, keeping both at the same GitHub Pages base.
export default defineConfig({
    site: 'https://caoalex-s.github.io',
    base: process.env.EXPLORER_BASE || '/',
    trailingSlash: 'always',
    output: 'static',
    devToolbar: { enabled: false },
});
