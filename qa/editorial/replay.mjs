/** Compare the live baseline and editorial candidate through ordinary controls.
 * Provide a Playwright module URL, baseline URL, candidate URL and output directory.
 * Uses separate browsers contexts for each route and viewport. Synthetic inputs only.
 */
import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';

const [playwright, baseline, candidate, output] = process.argv.slice(2);
assert.ok(playwright && baseline && candidate && output);
const { chromium } = await import(playwright);
const browser = await chromium.launch();
await mkdir(output, { recursive: true });
const evidence = [];
const routes = [
    {name:'sandbox', path:'#sandbox', drawing:'#canvas'},
    {name:'practice', path:'#practice', drawing:'#canvas'},
    {name:'learn', path:'learn/', heading:'main h1'},
    {name:'beam-lesson', path:'learn/beam-basics/', drawing:'#support-drawing'},
    {name:'portal', path:'?exercise=portal-absolute-moment#sandbox', drawing:'#canvas'},
    {name:'ideal-truss', path:'?exercise=ideal-planar-truss', drawing:'#truss-canvas'},
    {name:'week04', path:'?exercise=week04-truss-sections', drawing:'#section-drawing'}
];

async function ready(page, base, route) {
    await page.goto(new URL(route.path, base).href);
    await page.locator(route.drawing ?? route.heading).waitFor();
    if (await page.locator('#workspace').count()) {
        await page.waitForFunction(() => !document.querySelector('#workspace')?.inert);
    }
    await page.evaluate(() => document.fonts.ready);
}

async function layout(page, route) {
    return page.evaluate(({ drawing }) => {
        const rect = selector => {
            const element = selector && document.querySelector(selector);
            if (!element || !element.getClientRects().length) return null;
            const { x, y, width, height } = element.getBoundingClientRect();
            return { x, y, width, height };
        };
        const heading = [...document.querySelectorAll('h1')].find(h => h.offsetWidth > 50 && h.offsetHeight > 10);
        const root = getComputedStyle(document.documentElement);
        return {
            viewport: window.innerWidth,
            scrollWidth: document.documentElement.scrollWidth,
            drawing: rect(drawing),
            heading: heading && { text:heading.textContent, font:getComputedStyle(heading).fontFamily },
            paper: root.getPropertyValue('--paper').trim(),
            ink: root.getPropertyValue('--ink').trim(),
            wideElements: [...document.querySelectorAll('main *')].filter(node => {
                const bounds = node.getBoundingClientRect();
                if (!bounds.width || bounds.right <= window.innerWidth + 2) return false;
                return !node.closest('.drawing-scroll,.katex-display,svg');
            }).slice(0,12).map(node => node.id || node.className)
        };
    }, route);
}

async function keyboardAndTouch(page, mobile) {
    const range = page.locator('#section-position');
    const previous = await range.inputValue();
    const priorDistance = await page.locator('#section-distance').innerText();
    await range.focus();
    await page.keyboard.press('PageDown');
    assert.notEqual(await range.inputValue(), previous, 'Keyboard did not move the section');
    assert.notEqual(await page.locator('#section-distance').innerText(), priorDistance);
    await page.keyboard.press('Tab');
    assert.ok(await page.evaluate(() => document.activeElement.matches(':focus-visible')));
    assert.ok(await page.evaluate(() => {
        const focused = getComputedStyle(document.activeElement);
        return focused.outlineStyle !== 'none' && parseFloat(focused.outlineWidth) > 0 || focused.boxShadow !== 'none';
    }), 'The next keyboard focus has no visible treatment');

    if (mobile) {
        const canvas = page.locator('#canvas');
        const member = canvas.locator('[data-object="member"] path.hit').first();
        await member.scrollIntoViewIfNeeded();
        const target = await member.evaluate(path => {
            const point = path.getPointAtLength(path.getTotalLength() * 0.35).matrixTransform(path.getScreenCTM());
            return { x: point.x, y: point.y };
        });
        await page.touchscreen.tap(target.x, target.y);
        await page.locator('#inspector').getByText(/Properties|Member|Stiffness/i).first().waitFor({timeout:5000});
    }

    await page.locator('#settings-button').focus();
    await page.keyboard.press('Enter');
    assert.equal(await page.locator('#settings').evaluate(dialog => dialog.open), true);
    await page.keyboard.press('Escape');
    assert.equal(await page.locator('#settings').evaluate(dialog => dialog.open), false);
}

async function revealSection(page, side) {
    if (side === 'right') await page.locator('#section-side').selectOption('right');
    for (const [member, force] of Object.entries({BC:'T',GC:'T',GF:'C'})) {
        await page.locator('#predict-' + member).selectOption(force);
    }
    await page.locator('#record-section').click();
    await page.locator('#reveal-section').focus();
    await page.keyboard.press('Enter');
    await page.waitForFunction(() => document.querySelector('#section-receipt')?.textContent, null, {timeout:150000});
    const receipt = JSON.parse(await page.locator('#section-receipt').textContent());
    assert.deepEqual(receipt.query, {cut:3,side,centre:'G'});
    const rows = await page.locator('#section-response [data-member]').evaluateAll(items =>
        items.map(row => [row.dataset.member, row.dataset.component, row.dataset.sense]));
    assert.deepEqual(rows,[['BC','1','T'],['GC','1','T'],['GF','-2','C']]);
    const arrows = await page.locator('#section-fbd [data-action]').evaluateAll(items => items.map(item => ({
        action:item.dataset.action,
        direction:[Number(item.dataset.directionX), Number(item.dataset.directionY)],
        stroke:item.querySelector('line').getAttribute('stroke')
    })));
    return {inputDigest:receipt.inputDigest, reportDigest:receipt.reportDigest, arrows};
}

try {
    for (const [phase, base] of [['before',baseline],['after',candidate]]) {
        for (const [size, viewport] of [['desktop',{width:1440,height:1000}],['mobile',{width:390,height:844}]]) {
            const mobile = size === 'mobile';
            for (const route of routes) {
                const context = await browser.newContext({viewport, isMobile:mobile, hasTouch:mobile});
                const page = await context.newPage();
                const errors = [];
                page.on('pageerror', error => errors.push(String(error)));
                try {
                    await ready(page, base, route);
                    const state = await layout(page,route);
                    const prefix = [phase,size,route.name].join('-');
                    await page.screenshot({path:join(output,prefix+'.png'), fullPage:true});
                    const item = { phase,size,route:route.name,state,errors };
                    evidence.push(item);
                    if (route.name==='sandbox' && phase==='after') await keyboardAndTouch(page,mobile);
                    if (route.name==='beam-lesson' && phase==='after') {
                        await page.locator('#support-case').selectOption('three-rollers');
                        assert.match(await page.locator('#support-result').innerText(), /horizontal|unstable/i);
                    }
                    if (route.name==='week04') {
                        item.solution = await revealSection(page,'right');
                        item.revealedLayout = await layout(page,route);
                        await page.screenshot({path:join(output,prefix+'-revealed.png'),fullPage:true});
                        await page.locator('#section-load').fill('-2');
                        assert.equal(await page.locator('#section-response').isVisible(), false);
                        assert.equal(await page.locator('#reveal-section').isEnabled(), false);
                    }
                    assert.deepEqual(errors, []);
                } catch (error) {
                    await page.screenshot({path:join(output,[phase,size,route.name,'failure'].join('-')+'.png'),fullPage:true}).catch(() => {});
                    evidence.push({phase,size,route:route.name,error:String(error.stack ?? error)});
                } finally {
                    await context.close();
                }
            }
        }
    }
    await writeFile(join(output,'editorial-review.json'),JSON.stringify(evidence,null,2));
    assert.ok(evidence.every(item => !item.error),'At least one route replay failed');
} finally {
    await browser.close();
}
