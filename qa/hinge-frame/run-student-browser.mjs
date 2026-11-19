import { chromium } from '../../.data/student-tools/node_modules/playwright/index.mjs';
import { runMemberDiagramStudentCases } from '../member-diagram/student-canvas-cases.mjs';
import { runSpringStudentCases } from '../frame-spring/student-canvas-cases.mjs';
import { runStudentCanvasCases } from './student-canvas-cases.mjs';
import { createHash } from 'node:crypto';
import { mkdir, writeFile } from 'node:fs/promises';

const [base, target] = process.argv.slice(2);
if (!base || !['published', 'stage2', 'stage3', 'springs', 'diagram'].includes(target)) throw Error('Expected site URL and review target.');
const browser = await chromium.launch({ headless: true });
try {
    const context = await browser.newContext({ viewport: { width: 1440, height: 1000 } });
    if (target === 'published') {
        const served = {};
        for (const path of ['', 'index.html', 'verification.json', 'portal-checker/bundle/manifest.json']) {
            const response = await context.request.get(new URL(path, base).href, { headers: { 'Cache-Control': 'no-cache' } });
            const body = await response.body();
            served[path || '/'] = { status: response.status(), url: response.url(), sha256: createHash('sha256').update(body).digest('hex'),
                ...(path === 'verification.json' && response.ok() ? { verification: JSON.parse(body) } : {}) };
        }
        await mkdir('.data/student-results', { recursive: true });
        await writeFile('.data/student-results/served.json', JSON.stringify(served, null, 2));
    }
    const page = await context.newPage();
    page.setDefaultTimeout(10000);
    const options = { page, base, target, output: '.data/student-results' };
    const result = target === 'diagram' ? await runMemberDiagramStudentCases(options) : target === 'springs' ? await runSpringStudentCases(options) : await runStudentCanvasCases(options);
    console.log(JSON.stringify(result, null, 2));
    if (result.errors.length || result.records.some(record => record.failure)) process.exitCode = 1;
} finally {
    await browser.close();
}
