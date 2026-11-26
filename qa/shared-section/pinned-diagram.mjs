import assert from 'node:assert/strict';
import { mkdir } from 'node:fs/promises';
import { join } from 'node:path';

const [moduleUrl, base, output] = process.argv.slice(2);
const { chromium } = await import(moduleUrl);
const browser = await chromium.launch();
await mkdir(output, {recursive:true});
try {
    for (const width of [1440,390]) {
        const page = await browser.newPage({viewport:{width,height:width===390 ? 844 : 1000}});
        await page.goto(base+'#sandbox');
        const pin = page.locator('#pin-diagram');
        await pin.click();
        const source = await page.locator('#pin-reference-source').textContent();
        await page.locator('#drawing-object').selectOption('load:P1');
        const magnitude = page.locator('[data-property="magnitude"]');
        await magnitude.fill('30');
        await magnitude.press('Tab');
        assert.match(await page.locator('#pin-reference').textContent(), /20 kN down.*40 kN·m/);
        assert.match(await page.locator('#pin-current').textContent(), /30 kN down.*60 kN·m/);
        // The two paths have the same baseline. Their screen ordinates must
        // have the physical amplitude ratio, even when the moment side flips.
        async function ordinate(which) {
            return page.locator('path[data-diagram="'+which+'"]').first().evaluate(path => {
                const values = path.getAttribute('d').match(/-?\d+(?:\.\d+)?(?:e[+-]?\d+)?/gi).map(Number);
                const y = values.filter((_,i) => i%2===1);
                return y.reduce((max,point) => Math.abs(point-y[0])>Math.abs(max) ? point-y[0] : max,0);
            });
        }
        const tension = await ordinate('pinned');
        assert.ok(Math.abs(tension / await ordinate('current') - 2/3)<1e-6);
        await page.locator('#moment-side').selectOption('compression');
        assert.ok(Math.abs(await ordinate('pinned')+tension)<1e-6);
        assert.ok(Math.abs(await ordinate('pinned') / await ordinate('current') - 2/3)<1e-6);
        await page.locator('#diagram-comparison').screenshot({path:join(output,'pin-'+width+'.png')});
        await page.locator('[data-layer="V"]').click();
        assert.equal(await page.locator('path[data-diagram="pinned"]').count(),0);
        assert.match(await page.locator('#pin-status').innerText(), /Select bending moment/);
        await page.locator('[data-layer="M"]').click();
        assert.equal(await page.locator('#pin-reference-source').textContent(),source);
        await pin.click();
        assert.equal(await page.locator('#diagram-comparison').isVisible(),false);
        await page.close();
    }
} finally { await browser.close(); }
