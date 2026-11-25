import assert from 'node:assert/strict';
import {mkdir, writeFile} from 'node:fs/promises';
import {join} from 'node:path';

const [moduleUrl,base,output] = process.argv.slice(2);
const {chromium} = await import(moduleUrl);
const browser = await chromium.launch();
await mkdir(output,{recursive:true});
try {
    for (const width of [1440,390]) {
        const page = await browser.newPage({viewport:{width,height:width===390?844:1000},hasTouch:width===390});
        await page.goto(base+'#sandbox');
        await page.waitForFunction(()=>document.querySelector('#workspace') && !document.querySelector('#workspace').inert);
        const touch = width===390 ? await page.context().newCDPSession(page) : null;
        const load = page.locator('#canvas [data-point-force][data-id="P1"]');
        const handle = page.locator('#canvas [data-rotate-force="P1"] circle').first();
        const canvas = page.locator('#canvas');
        const model = () => page.evaluate(()=>JSON.parse(localStorage.getItem('cv2011-model')).loads.find(l=>l.id==='P1'));
        const tap = async (x,y) => touch ? page.touchscreen.tap(x,y) : page.mouse.click(x,y);
        async function point(x,y,phase) {
            if (touch) {
                const type = {down:'touchStart',move:'touchMove',up:'touchEnd'}[phase];
                await touch.send('Input.dispatchTouchEvent',{type,touchPoints:phase==='up'?[]:[{x,y}]});
            } else {
                await page.mouse.move(x,y);
                if (phase==='down') await page.mouse.down();
                if (phase==='up') await page.mouse.up();
            }
        }
        assert.equal(await handle.count(),0);
        await canvas.scrollIntoViewIfNeeded();
        const shaft = await load.locator('path.hit').evaluate(path=>{
            const p=path.getPointAtLength(path.getTotalLength()*.55).matrixTransform(path.getScreenCTM());
            return [p.x,p.y];
        });
        await tap(...shaft);
        await handle.waitFor();
        await canvas.scrollIntoViewIfNeeded();
        const origin=await load.locator('[data-vector="force"]').evaluate(g=>{
            const p=new DOMPoint(+g.dataset.originX,+g.dataset.originY).matrixTransform(g.getScreenCTM());
            return [p.x,p.y];
        });
        const box=await handle.boundingBox();
        const hx=box.x+box.width/2, hy=box.y+box.height/2;
        const radius=Math.hypot(hx-origin[0],hy-origin[1]);
        await point(hx,hy,'down');
        for(const degrees of [285,315,350,15,30]) {
            const radians=degrees*Math.PI/180;
            await point(origin[0]-radius*Math.cos(radians),origin[1]+radius*Math.sin(radians),'move');
        }
        assert.ok(await page.locator('#canvas .rotate-angle').isVisible());
        await page.waitForFunction(() => {
            const force=JSON.parse(localStorage.getItem('cv2011-model')).loads.find(l=>l.id==='P1');
            return Math.abs(Math.atan2(force.fy,force.fx)*180/Math.PI-30)<3;
        });
        const rotated=await model();
        const angle=Math.atan2(rotated.fy,rotated.fx)*180/Math.PI;
        assert.ok(Math.abs(angle-30)<3,JSON.stringify({width,angle}));
        assert.equal(rotated.t,.5);
        assert.ok(Math.abs(Math.hypot(rotated.fx,rotated.fy)-20)<1e-10);
        await page.screenshot({path:join(output,'rotating-'+width+'.png')});
        await point(origin[0]-radius*Math.cos(Math.PI/6),origin[1]+radius*.5,'up');
        assert.equal(await page.locator('#canvas .rotate-angle').count(),0);
        const annotation=load.locator('[data-force-annotation]');
        if(touch) await annotation.tap(); else await annotation.click();
        assert.ok(await page.locator('body').evaluate(el=>el.classList.contains('point-quick-edit')));
        const field=key=>page.locator('#inspector [data-property="'+key+'"]');
        await field('pointAngle').fill('30');
        await field('pointAngle').press('Tab');
        await field('magnitude').fill('40');
        await field('magnitude').press('Tab');
        const final=await model();
        assert.ok(Math.abs(final.fx-20*Math.sqrt(3))<1e-10 && Math.abs(final.fy-20)<1e-10);
        assert.equal(final.t,.5);
        assert.ok(await page.locator('#inspector [data-range=magnitude]').isVisible());
        await page.screenshot({path:join(output,'exact-'+width+'.png')});
        await page.locator('#full-point-properties').click();
        assert.ok(await page.locator('#inspector .direction-dial').isVisible());
        await page.reload();
        assert.deepEqual(await model(),final);
        await writeFile(join(output,'result-'+width+'.json'),JSON.stringify({width,rotated,final},null,2));
        await touch?.detach();
        await page.close();
    }
} finally {await browser.close();}
