import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';

const [moduleUrl, base, output] = process.argv.slice(2);
const { chromium } = await import(moduleUrl);
const browser = await chromium.launch();
await mkdir(output,{recursive:true});
try {
    for (const width of [1440,390]) {
        const page = await browser.newPage({viewport:{width,height:width===390?844:1000},hasTouch:width===390});
        const errors=[];
        page.on('pageerror', error=>errors.push(String(error)));
        const prop = key => page.locator('#inspector [data-property="'+key+'"]');
        const checked = key => page.locator(`#inspector input[name="${key}"]:checked`);
        async function choose(key, value) {
            const label = page.locator(`#inspector label:has(input[name="${key}"][value="${value}"])`);
            if (width === 390) await label.tap();
            else await label.click();
            assert.equal(await checked(key).count(), 1);
            assert.equal(await checked(key).inputValue(), value);
        }
        const picker = page.locator('#drawing-object');
        async function edit(key,value) {
            const control = prop(key);
            await control.fill(String(value));
            await control.press('Tab');
        }
        async function state() {
            return page.evaluate(()=>JSON.parse(localStorage.getItem('cv2011-model')));
        }
        async function open(model, version) {
            await page.locator('#model-file').setInputFiles({name:'direction.json', mimeType:'application/json',
                buffer:Buffer.from(JSON.stringify({version,model}))});
            await page.waitForFunction(expected=>JSON.parse(localStorage.getItem('cv2011-model'))?.loads[0].id===expected,model.loads[0].id);
        }
        await page.goto(base+'#sandbox');
        await page.waitForFunction(()=>!document.querySelector('#workspace')?.inert);
        await picker.selectOption({label:'P₁ · Point force'});
        assert.equal(await checked('pointDirection').inputValue(), '270');
        assert.equal(await prop('pointAngle').isVisible(), false);
        await choose('pointDirection','custom');
        await page.keyboard.press('Tab');
        assert.ok(await prop('pointAngle').evaluate(el => el === document.activeElement));
        await edit('pointAngle',37);
        assert.equal(await checked('pointDirection').inputValue(), 'custom');
        await choose('pointDirection','0');
        await page.locator('.force-components > summary').click();
        assert.equal(await prop('fx').inputValue(), '20');
        assert.equal(await prop('fy').inputValue(), '0');
        const point = (await state()).loads[0];
        assert.deepEqual([point.fx,point.fy],[20,0]);
        await edit('magnitude',30);
        await checked('pointDirection').focus();
        await page.keyboard.press('ArrowRight');
        assert.equal(await checked('pointDirection').inputValue(), '90');
        assert.ok(await checked('pointDirection').evaluate(el => el === document.activeElement));
        assert.deepEqual((await state()).loads.map(({fx,fy})=>[fx,fy]),[[0,30]]);
        await page.locator('#frame-generate').click();
        await page.waitForFunction(()=>{try {return JSON.parse(document.querySelector('#portal-certificate').textContent).sourceRequest.model.loads[0].fy===30;}catch{return false;}},null,{timeout:120000});
        await picker.selectOption('load:'+point.id);
        await checked('pointDirection').scrollIntoViewIfNeeded();
        await page.screenshot({path:join(output,'point-'+width+'.png')});

        const range = key => page.locator(`#inspector input[data-range="${key}"]`);
        async function dragRange(key) {
            const slider = range(key);
            await slider.scrollIntoViewIfNeeded();
            const box = await slider.boundingBox();
            const y = box.y + box.height / 2;
            const x = fraction => box.x + box.width * fraction;
            const cdp = width === 390 ? await page.context().newCDPSession(page) : null;
            if (cdp) await cdp.send('Input.dispatchTouchEvent', {type:'touchStart',touchPoints:[{x:x(.34),y}]});
            else { await page.mouse.move(x(.34),y); await page.mouse.down(); }
            const initial = await slider.inputValue();
            for (const fraction of [.5,.67,.81]) {
                if (cdp) await cdp.send('Input.dispatchTouchEvent',{type:'touchMove',touchPoints:[{x:x(fraction),y}]});
                else await page.mouse.move(x(fraction),y);
            }
            const during = Number(await slider.inputValue());
            assert.notEqual(String(during), initial);
            assert.equal(Number(await prop(key).inputValue()), during);
            assert.equal((await state()).loads[0].fy, during);
            assert.equal(await page.locator('#portal-certificate').textContent(),'');
            if (cdp) { await cdp.send('Input.dispatchTouchEvent',{type:'touchEnd',touchPoints:[]}); await cdp.detach(); }
            else await page.mouse.up();
            return during;
        }
        const dragged = await dragRange('magnitude');
        await page.getByRole('button',{name:'Undo',exact:true}).click();
        assert.equal((await state()).loads[0].fy,30);
        await page.getByRole('button',{name:'Redo',exact:true}).click();
        assert.equal((await state()).loads[0].fy,dragged);
        await picker.selectOption('load:'+point.id);
        await edit('magnitude',257.25);
        assert.ok(Number(await range('magnitude').getAttribute('max')) >= 257.25);
        await range('magnitude').focus();
        await page.keyboard.press('ArrowLeft');
        assert.ok(await range('magnitude').evaluate(el=>el===document.activeElement));
        assert.ok((await state()).loads[0].fy < 257.25);
        await page.reload();
        await picker.selectOption('load:'+point.id);
        assert.equal(Number(await range('magnitude').inputValue()), (await state()).loads[0].fy);

        async function place(tool, stations) {
            const toolbox = page.locator('#drawing-toolbox');
            if (await toolbox.getAttribute('open') === null) await toolbox.locator(':scope > summary').click();
            await page.locator(`button[data-tool="${tool}"]`).click();
            const memberPath = page.locator('#canvas [data-object="member"] path').first();
            await page.locator('#canvas').scrollIntoViewIfNeeded();
            for (const station of stations) {
                const [x,y] = await memberPath.evaluate((el,t) => {
                    const p = el.getPointAtLength(el.getTotalLength()*t).matrixTransform(el.getScreenCTM());
                    return [p.x,p.y];
                },station);
                if (width === 390) await page.touchscreen.tap(x,y);
                else await page.mouse.click(x,y);
            }
            assert.equal((await state()).loads.at(-1).kind,tool);
        }
        await place('moment',[.3]);
        assert.ok(await page.getByLabel('Magnitude (kN m)', {exact:true}).isVisible());
        await choose('momentSense','-1');
        assert.equal((await state()).loads.at(-1).mz,-20);
        await page.screenshot({path:join(output,'moment-'+width+'.png')});
        await range('momentMagnitude').focus();
        await page.keyboard.press('ArrowRight');
        assert.ok((await state()).loads.at(-1).mz < -20);
        await edit('momentMagnitude',0);
        await choose('momentSense','1');
        await edit('momentMagnitude',12);
        assert.equal((await state()).loads.at(-1).mz,12);
        await place('distributed',[.2,.7]);
        assert.ok(await prop('qEnd').isVisible());
        assert.equal(await prop('lineAngle').inputValue(), '270');
        await range('qEnd').focus();
        await page.keyboard.press('Home');
        assert.equal((await state()).loads.at(-1).qEnd,20);
        await choose('lineReference','180');
        assert.equal((await state()).loads.at(-1).direction,180);
        await place('force',[.8]);
        assert.ok(await prop('magnitude').isVisible());
        const model=await state();
        const member=model.members[0].id;
        model.nodes[1].x=3; model.nodes[1].y=4;
        model.supports=[{...model.supports[0],kind:'fixed'}];
        model.loads=[{id:'line',label:'w_1',member,kind:'distributed',t:0,end:1,fx:0,fy:-2,qEnd:-4,mz:0}];
        await open(model,2);
        await picker.selectOption('load:line');
        await choose('lineReference','custom');
        await edit('lineAngle',0);
        await edit('fy',-2);
        assert.deepEqual((await state()).loads.map(({direction,fy,qEnd})=>[direction,fy,qEnd]),[[0,-2,4]]);
        await page.locator('#frame-generate').click();
        assert.match(await page.locator('#frame-worked-output').innerText(),/Numerical section response/);
        assert.equal(await page.locator('#portal-certificate').textContent(),'');
        await choose('lineReference','normal');
        assert.equal((await state()).loads[0].direction,'member-normal');
        assert.equal(await page.locator('#frame-worked-output').textContent(),'');
        await page.getByRole('button',{name:'Undo',exact:true}).click();
        assert.equal((await state()).loads[0].direction,0);
        await picker.selectOption('load:line');
        await choose('lineReference','normal');
        const fileMenu=page.locator('.model-files');
        if (await fileMenu.getAttribute('open') === null) await fileMenu.locator('summary').click();
        const downloaded=page.waitForEvent('download');
        await page.locator('#export-model').click();
        const file=await downloaded;
        const stream=await file.createReadStream();
        const chunks=[];
        for await(const chunk of stream) chunks.push(chunk);
        const exported=JSON.parse(Buffer.concat(chunks));
        assert.equal(exported.version,3);
        assert.equal(exported.model.loads[0].direction,'member-normal');
        await page.reload();
        await picker.selectOption('load:line');
        assert.equal(await checked('lineReference').inputValue(),'normal');
        exported.model.loads[0].id='reversed';
        exported.model.nodes[1].x=-3;exported.model.nodes[1].y=-4;
        await open(exported.model,3);
        await picker.selectOption('load:reversed');
        const paths=await page.locator('#canvas [data-object="load"] [data-vector="force"] path[stroke]').evaluateAll(items=>items.map(item=>item.getAttribute('d')));
        const last=paths.at(-1).match(/[-+\d.e]+/g).map(Number);
        assert.ok(last[2]>last[0] && last[3]>last[1], 'Reversed member normal must point right and down');
        assert.match(await page.locator('#section-free-body-content').textContent(),/intensity along local/);
        assert.equal(await page.evaluate(()=>document.documentElement.scrollWidth),width);
        await checked('lineReference').scrollIntoViewIfNeeded();
        await page.screenshot({path:join(output,'line-'+width+'.png')});
        assert.deepEqual(errors,[]);
        await writeFile(join(output,'result-'+width+'.json'),JSON.stringify({width,point,exported,errors},null,2));
        await page.close();
    }
} finally {await browser.close();}
