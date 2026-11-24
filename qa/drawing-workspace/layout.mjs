import assert from 'node:assert/strict';
import { chromium } from '../../.data/student-tools/node_modules/playwright/index.mjs';

const browser = await chromium.launch();
try {
    for (const width of [1440, 900, 390, 320]) {
        const page = await browser.newPage({ viewport: { width, height: width > 750 ? 1000 : 844 } });
        await page.goto('http://127.0.0.1:8765/#sandbox');
        await page.locator('#drawing-object').waitFor();
        await page.evaluate(() => document.fonts.ready);
        const beam = await page.locator('#canvas [data-object="member"]').first().boundingBox();
        assert.ok(beam && beam.y > 0 && beam.y + beam.height < (width > 750 ? 1000 : 844), 'Beam must fit on opening at ' + width);
        assert.equal(await page.evaluate(() => document.documentElement.scrollWidth), width);
        const station = [String.raw`x = 4\,\mathrm{m}`, String.raw`L = 8\,\mathrm{m}`];
        const tex = 'annotation[encoding="application/x-tex"]';
        assert.deepEqual(await page.locator('#section-distance').locator(tex).allTextContents(), station);
        if (width <= 750) {
            const strip = page.locator('.cut-readout');
            assert.deepEqual((await strip.locator(tex).allTextContents()).slice(0, 2), station);
            assert.ok(await strip.evaluate(e => e.scrollWidth <= e.clientWidth));
        }
        const picker = page.locator('#drawing-object');
        await picker.focus();
        await page.keyboard.press('Home');
        await page.keyboard.press('ArrowDown');
        const force = page.locator('#inspector [data-property="magnitude"]');
        for (let i = 0; i < 5 && !await force.evaluate(e => e === document.activeElement); i++)
            await page.keyboard.press('Tab');
        assert.ok(await force.evaluate(e => e === document.activeElement), 'Tab from object selector to force magnitude at ' + width);
        await force.fill('30');
        await page.keyboard.press('Tab');
        await page.waitForFunction(() => document.querySelector('#section-results .is-current strong')?.textContent.includes('60'));
        await page.waitForFunction(() => document.activeElement !== document.body);
        await page.locator('.drawing-utilities > summary').click();
        await page.locator('[data-mode="practice"]').click();
        assert.equal(await page.locator('#drawing-object').count(), 0);
        await page.locator('[data-mode="sandbox"]').click();
        await page.locator('#drawing-object').waitFor();
        assert.equal(await page.locator('[data-property="fy"]').inputValue(), '-30');
        await page.locator('.drawing-utilities summary').click();
        await page.keyboard.press('Escape');
        assert.equal(await page.locator('.drawing-utilities').getAttribute('open'), null);
        await page.close();
    }
} finally { await browser.close(); }
