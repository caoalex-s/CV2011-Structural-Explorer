import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';

const [moduleUrl, base, output] = process.argv.slice(2);
const { chromium } = await import(moduleUrl);
const browser = await chromium.launch();
const reports = [];
await mkdir(output, { recursive: true });
try {
    for (const width of [1440, 390]) {
        const page = await browser.newPage({ viewport: { width, height: width === 390 ? 844 : 1000 } });
        await page.goto(base + '#sandbox');
        await page.waitForFunction(() => !document.querySelector('#workspace')?.inert);
        await page.locator('#frame-parameter').fill('0.653');
        await page.locator('#frame-generate').click();
        await page.locator('#frame-worked-output h3').first().waitFor({ timeout: 120000 });
        await page.evaluate(() => document.fonts.ready);
        const formulas = selector => page.locator(selector + ' annotation').allTextContents();
        const metre = String.raw`\,\mathrm{m}`;
        const force = String.raw`\,\mathrm{kN}`;
        const moment = force + metre;
        assert.deepEqual(await formulas('.fbd-values'), ['N = 0'+force,'V = -10'+force,'M = 27.76'+moment]);
        assert.deepEqual(await formulas('#checked-section'), ['x = 5.22'+metre, 'L = 8'+metre]);
        assert.ok((await formulas('#section-free-body figcaption')).includes('x = 5.22'+metre));
        assert.deepEqual(await formulas('#fbd-description'), ['x']);
        const worked = await formulas('#frame-worked-output');
        for (const symbol of ['t = 0.653','x','y','N','M',String.raw`\mathrm{d}M/\mathrm{d}x = V`]) assert.ok(worked.includes(symbol),symbol);
        assert.ok(await page.locator('.section-fbd-math msub').count());
        assert.match(await page.locator('#section-fbd').getAttribute('aria-label'),/5.22 m/);
        assert.equal(await page.locator('.math-error').count(),0);
        assert.ok(await page.evaluate(() => document.documentElement.scrollWidth === innerWidth));
        await page.locator('#section-free-body figure').screenshot({ path: join(output,'fbd-'+width+'.png') });
        await page.locator('#frame-worked-output h3').first().scrollIntoViewIfNeeded();
        await page.screenshot({ path: join(output,'worked-'+width+'.png') });
        reports.push({width,station:0.653,values:await formulas('.fbd-values')});
        await page.close();
    }
    await writeFile(join(output,'notation.json'),JSON.stringify(reports,null,2));
} finally { await browser.close(); }
