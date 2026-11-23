/** Check the phone disclosures and the checked workspace under its own URL. */
import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
import { chromium } from '../../.data/student-tools/node_modules/playwright/index.mjs';

const base = 'http://127.0.0.1:8765/';
const output = '.data/editorial-evidence/navigation';
await mkdir(output, {recursive:true});
const browser = await chromium.launch();
try {
    const page = await browser.newPage({viewport:{width:390,height:844}, hasTouch:true, isMobile:true});
    const errors = [];
    page.on('pageerror', error => errors.push(String(error)));
    await page.goto(base);
    await page.waitForFunction(() => !document.querySelector('#workspace').inert);
    const beam = await page.locator('#canvas [data-object="member"]').first().boundingBox();
    assert.ok(beam && beam.y >= 0 && beam.y + beam.height <= 844, 'Initial beam must fit on the phone screen');
    for (const [disclosure, control] of [
        ['.exercise-directory', 'a[href*="week04"]'], ['.model-files', '#import-model'], ['#drawing-toolbox', '[data-tool="member"]']
    ]) {
        const group = page.locator(disclosure);
        const summary = group.locator(':scope > summary');
        await summary.focus();
        await page.keyboard.press('Enter');
        assert.ok(await group.locator(control).isVisible());
        await page.keyboard.press('Enter');
        assert.equal(await group.locator(control).isVisible(), false);
    }
    await page.locator('#settings-button').click();
    await page.screenshot({path:output+'/mobile-settings.png'});
    await page.keyboard.press('Escape');
    await page.locator('[data-mode="insights"]').click();
    await page.locator('#insights-panel h2').first().waitFor();
    await page.screenshot({path:output+'/mobile-insights.png',fullPage:true});
    await page.goto(new URL('portal-checker/', base).href);
    await page.waitForFunction(() => !document.querySelector('#workspace').inert);
    assert.equal(await page.locator('#page-title').innerText(), 'Checked portal workspace');
    assert.equal(new URL(await page.getByRole('link',{name:'Main workspace'}).getAttribute('href'),page.url()).href, base);
    await page.screenshot({path:output+'/mobile-checked-portal.png'});
    assert.deepEqual(errors,[]);
    await writeFile(output+'/navigation.json',JSON.stringify({beam,viewport:{width:390,height:844},errors},null,2));
} finally {
    await browser.close();
}
