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
        async function assertDirection(x, y) {
            const svg = page.locator('#inspector .direction-dial');
            const axis = await svg.locator('.indicator-pointer').evaluate(pointer => {
                const matrix = pointer.getScreenCTM();
                const length = Math.hypot(matrix.a, matrix.b);
                return [matrix.a/length, -matrix.b/length];
            });
            assert.ok(Math.hypot(axis[0]-x, axis[1]-y)<1e-6, JSON.stringify({axis,x,y}));
        }
        await page.goto(base+'#sandbox');
        await page.waitForFunction(()=>!document.querySelector('#workspace')?.inert);
        await picker.selectOption({label:'P₁ · Point force'});
        const dial = page.locator('#inspector .direction-dial');
        await assertDirection(0,-1);
        await dial.focus();
        await page.keyboard.press('ArrowRight');
        assert.equal(await dial.getAttribute('aria-valuenow'),'271');
        await page.keyboard.press('Tab');
        assert.ok(await prop('pointAngle').evaluate(el => el === document.activeElement));
        await edit('pointAngle',46.25);
        await assertDirection(Math.cos(46.25*Math.PI/180),Math.sin(46.25*Math.PI/180));
        await edit('pointAngle',0);
        await page.locator('.force-components > summary').click();
        assert.equal(await prop('fx').inputValue(), '20');
        assert.equal(await prop('fy').inputValue(), '0');
        const forceLabel = page.locator('#canvas [data-object="load"] [data-vector="force"] text').first();
        const reactionLabel = page.locator('#canvas [data-horizontal-reaction] text').first();
        await page.evaluate(() => document.fonts.ready);
        const bounds = locator => locator.evaluate(el => el.getBoundingClientRect().toJSON());
        const [forceBox, reactionBox] = await Promise.all([bounds(forceLabel),bounds(reactionLabel)]);
        assert.ok(forceBox.left >= reactionBox.right || reactionBox.left >= forceBox.right
            || forceBox.top >= reactionBox.bottom || reactionBox.top >= forceBox.bottom,
            JSON.stringify({width, forceBox, reactionBox}));
        const point = (await state()).loads[0];
        assert.deepEqual([point.fx,point.fy],[20,0]);
        await edit('magnitude',30);
        await dial.focus();
        await page.keyboard.press('PageUp');
        await page.keyboard.press('PageUp');
        assert.equal(await dial.getAttribute('aria-valuenow'),'90');
        assert.ok(await dial.evaluate(el => el === document.activeElement));
        assert.deepEqual((await state()).loads.map(({fx,fy})=>[fx,fy]),[[0,30]]);
        await page.locator('#frame-generate').click();
        await page.waitForFunction(()=>{try {return JSON.parse(document.querySelector('#portal-certificate').textContent).sourceRequest.model.loads[0].fy===30;}catch{return false;}},null,{timeout:120000});
        await picker.selectOption('load:'+point.id);
        await dial.scrollIntoViewIfNeeded();
        await page.screenshot({path:join(output,'point-'+width+'.png')});

        const dialBox = await dial.boundingBox();
        const touch = width === 390 ? await page.context().newCDPSession(page) : null;
        async function pointAt(degrees, phase) {
            const angle = degrees*Math.PI/180;
            const x = dialBox.x + dialBox.width*(.5 + 40/128*Math.cos(angle));
            const y = dialBox.y + dialBox.height*(.5 - 40/128*Math.sin(angle));
            if (touch) {
                const type = {down:'touchStart',move:'touchMove',up:'touchEnd'}[phase];
                await touch.send('Input.dispatchTouchEvent',{type,touchPoints:phase==='up'?[]:[{x,y}]});
            } else {
                await page.mouse.move(x,y);
                if (phase==='down') await page.mouse.down();
                if (phase==='up') await page.mouse.up();
            }
        }
        await pointAt(90,'down');
        await pointAt(43.5,'move');
        assert.equal(await dial.getAttribute('aria-valuenow'),'45');
        assert.equal(await page.locator('#portal-certificate').textContent(),'');
        await pointAt(49,'move');
        assert.equal(await dial.getAttribute('aria-valuenow'),'45');
        await pointAt(55,'move');
        assert.ok(Math.abs(Number(await dial.getAttribute('aria-valuenow'))-55)<2);
        await pointAt(359,'move');
        assert.equal(await dial.getAttribute('aria-valuenow'),'0');
        await pointAt(3,'move');
        assert.equal(await dial.getAttribute('aria-valuenow'),'0');
        await pointAt(3,'up');
        await touch?.detach();
        await page.getByRole('button',{name:'Undo',exact:true}).click();
        assert.equal((await state()).loads[0].fy,30);
        await picker.selectOption('load:'+point.id);

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
        await edit('lineAngle',180);
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
        await edit('lineAngle',0);
        await edit('fy',-2);
        assert.deepEqual((await state()).loads.map(({direction,fy,qEnd})=>[direction,fy,qEnd]),[[0,-2,4]]);
        await page.locator('#frame-generate').click();
        assert.match(await page.locator('#frame-worked-output').innerText(),/Numerical section response/);
        assert.equal(await page.locator('#portal-certificate').textContent(),'');
        await choose('lineReference','normal');
        assert.equal((await state()).loads[0].direction,'member-normal');
        await assertDirection(-.8,.6);
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
        await assertDirection(.8,-.6);
        assert.ok(await page.getByRole('group',{name:'Positive intensity direction',exact:true}).isVisible());
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
