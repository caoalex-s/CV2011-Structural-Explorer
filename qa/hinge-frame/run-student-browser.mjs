import { chromium } from '../../.data/student-tools/node_modules/playwright/index.mjs';
import { runStudentCanvasCases } from './student-canvas-cases.mjs';

const [base, target] = process.argv.slice(2);
if (!base || !['published', 'stage2'].includes(target)) throw Error('Expected site URL and review target.');
const browser = await chromium.launch({ headless: true });
try {
    const context = await browser.newContext({ viewport: { width: 1440, height: 1000 } });
    const page = await context.newPage();
    page.setDefaultTimeout(10000);
    const result = await runStudentCanvasCases({ page, base, target, output: '.data/student-results' });
    console.log(JSON.stringify(result, null, 2));
    if (result.errors.length || result.records.some(record => record.error)) process.exitCode = 1;
} finally {
    await browser.close();
}
