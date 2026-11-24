/** Independent load-edit workflow in matched desktop and phone viewports. */
import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';

const [playwright, baseline, candidate, out] = process.argv.slice(2);
assert.ok(playwright && baseline && candidate && out);
const { chromium } = await import(playwright);
const browser = await chromium.launch();
await mkdir(out, { recursive: true });
const results = [];
const viewports = { desktop: {width:1440,height:1000}, phone:{width:390,height:844} };
const normalize = text => text.replaceAll('−','-').replace(/\s+/g,' ').trim();

async function measure(page) {
    return page.evaluate(() => {
        const box = selector => {
            const node = document.querySelector(selector);
            const rect = node?.getBoundingClientRect();
            if (!rect || !rect.height || !rect.width) return null;
            return {x:rect.x,y:rect.y,width:rect.width,height:rect.height,
                inView:rect.y >= 0 && rect.bottom <= innerHeight};
        };
        return {viewport:{width:innerWidth,height:innerHeight}, scrollWidth:document.documentElement.scrollWidth,
            scrollY, canvas:box('#canvas'), editor:box('#inspector [data-property="fy"]'),
            propertiesControl:box('#edit-selection'), results:box('#section-results')};
    });
}

async function selectForceOnDrawing(page, input) {
    const arrow = page.locator('#canvas [data-object="load"] [data-vector="force"] path.hit').first();
    await arrow.scrollIntoViewIfNeeded();
    const point = await arrow.evaluate(path => {
        const position = path.getPointAtLength(path.getTotalLength() * .45).matrixTransform(path.getScreenCTM());
        const target = document.elementFromPoint(position.x, position.y)?.closest('[data-object="load"]');
        return {x:position.x,y:position.y,load:target?.dataset.id};
    });
    assert.ok(point.load, 'Force arrow is covered or not selectable');
    if (input === 'touch') await page.touchscreen.tap(point.x,point.y);
    else await page.mouse.click(point.x,point.y);
}

async function selectForceByKeyboard(page) {
    const selector = page.locator('#drawing-object');
    await selector.waitFor({state:'visible'});
    const target = await selector.locator('option').evaluateAll(options =>
        options.findIndex(option => /point force|\bP[_ ]?1\b/i.test(option.textContent)));
    assert.ok(target >= 0, 'Object list has no named point force');
    await selector.focus();
    await page.keyboard.press('Home');
    for (let index=0; index<target; index++) await page.keyboard.press('ArrowDown');
    assert.equal(await selector.evaluate(element => element.selectedIndex),target);
}

async function verifyResults(page, expectedShear, expectedMoment, phase) {
    const text = normalize(await page.locator('#section-results').innerText());
    const metrics = page.locator('#section-results .metric');
    if (phase === 'after') {
        assert.deepEqual((await metrics.locator('annotation[encoding="application/x-tex"]').allTextContents()).slice(1, 3), ['V', 'M']);
    }
    assert.equal((await metrics.nth(1).locator('strong').innerText()).replaceAll('−','-').replace(/\s+/g,' '), expectedShear + ' kN');
    assert.equal((await metrics.nth(2).locator('strong').innerText()).replaceAll('−','-').replace(/\s+/g,' '), expectedMoment + ' kN m');
    return text;
}

async function replay(phase,base,size,input) {
    const context = await browser.newContext({viewport:viewports[size],isMobile:size==='phone',hasTouch:size==='phone'});
    const page = await context.newPage();
    const errors=[], posts=[];
    page.on('pageerror', error => errors.push(String(error)));
    page.on('request', request => { if(request.method()==='POST')posts.push(new URL(request.url()).pathname); });
    const prefix = [phase,size,input].join('-');
    try {
        await page.goto(new URL('#sandbox',base).href);
        await page.waitForFunction(() => !document.querySelector('#workspace')?.inert);
        await page.locator('#canvas [data-object="load"]').waitFor();
        await page.evaluate(() => document.fonts.ready);
        const initial = await measure(page);
        const before = await verifyResults(page,-10,40,phase);
        await page.screenshot({path:join(out,prefix+'-initial.png')});

        if (input==='keyboard') await selectForceByKeyboard(page);
        else await selectForceOnDrawing(page,input);
        const selected = await measure(page);
        await page.screenshot({path:join(out,prefix+'-selected.png')});
        const editor = page.locator('#inspector [data-property="fy"]');
        await editor.waitFor({state:'visible'});
        assert.equal(await editor.inputValue(),'-20');
        const name = await editor.evaluate(element => Array.from(element.labels, label => label.textContent.trim()).join(' '));
        assert.match(name,/Vertical force/i);
        assert.match(name,/upward/i);

        if (input==='keyboard') {
            for(let i=0;i<32 && !await editor.evaluate(node=>node===document.activeElement);i++) {
                await page.keyboard.press('Tab');
            }
            assert.equal(await editor.evaluate(node=>node===document.activeElement),true,'Keyboard cannot reach the force field');
            await page.keyboard.press('Control+a');
            await page.keyboard.type('-30');
        } else {
            await editor.fill('-30');
        }
        await page.keyboard.press('Tab'); // commit the edit
        await page.waitForFunction(() =>
            JSON.parse(localStorage.getItem('cv2011-model') ?? '{}').loads?.[0]?.fy === -30);
        const focusAfterEdit = await page.evaluate(() => {
            const active = document.activeElement;
            return active.id || active.getAttribute('data-property') || active.tagName;
        });
        const changed = await verifyResults(page,-15,60,phase);
        const persisted = await page.evaluate(() => JSON.parse(localStorage.getItem('cv2011-model')));
        assert.equal(persisted.loads[0].t,.5);
        assert.equal(persisted.loads[0].fx,0);
        const forceLabel = normalize(await page.locator('#canvas [data-object="load"] [data-vector="force"] text').first().textContent());
        assert.match(forceLabel,/30\s*kN/);
        await page.screenshot({path:join(out,prefix+'-edited.png'),fullPage:true});
        const response = await measure(page);
        const layer = page.locator('#layers [data-layer="V"]');
        await layer.focus();
        await page.keyboard.press('Enter');
        assert.equal(await layer.getAttribute('aria-pressed'),'true');
        const shearLabel = normalize(await page.locator('#canvas .svg-value').first().textContent());
        assert.match(shearLabel,/15\s*kN/);
        await page.locator('#undo').click();
        const undone = await verifyResults(page,-10,40,phase);
        assert.deepEqual(errors,[]);
        assert.deepEqual(posts,[]);
        assert.equal(response.scrollWidth,response.viewport.width);
        results.push({phase,size,input,initial,selected,response,before,changed,undone,forceLabel,shearLabel,focusAfterEdit,errors,posts});
    } catch(error) {
        await page.screenshot({path:join(out,prefix+'-failure.png'),fullPage:true}).catch(()=>{});
        results.push({phase,size,input,error:String(error.stack??error),errors,posts});
    } finally { await context.close(); }
}

try {
    for (const [phase,base] of [['before',baseline],['after',candidate]]) {
        await replay(phase,base,'desktop','mouse');
        await replay(phase,base,'phone','touch');
    }
    await replay('after',candidate,'desktop','keyboard');
    await writeFile(join(out,'sandbox-interaction-review.json'),JSON.stringify(results,null,2));
    assert.ok(results.every(result=>!result.error),'A load-edit replay failed. See the output JSON.');
} finally { await browser.close(); }
