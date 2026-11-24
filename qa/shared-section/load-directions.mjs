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
        await edit('pointAngle',0);
        const point = (await state()).loads[0];
        assert.deepEqual([point.fx,point.fy],[20,0]);
        await edit('magnitude',30);
        await edit('pointAngle',90);
        assert.deepEqual((await state()).loads.map(({fx,fy})=>[fx,fy]),[[0,30]]);
        await page.locator('#frame-generate').click();
        await page.waitForFunction(()=>{try {return JSON.parse(document.querySelector('#portal-certificate').textContent).sourceRequest.model.loads[0].fy===30;}catch{return false;}},null,{timeout:120000});
        await picker.selectOption('load:'+point.id);
        await prop('pointAngle').scrollIntoViewIfNeeded();
        await page.screenshot({path:join(output,'point-'+width+'.png')});

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
        await prop('lineReference').selectOption('normal');
        assert.equal((await state()).loads[0].direction,'member-normal');
        assert.equal(await page.locator('#frame-worked-output').textContent(),'');
        await page.getByRole('button',{name:'Undo',exact:true}).click();
        assert.equal((await state()).loads[0].direction,0);
        await picker.selectOption('load:line');
        await prop('lineReference').selectOption('normal');
        const fileMenu=page.locator('.model-files');
        if (!(await fileMenu.getAttribute('open')!==null)) await fileMenu.locator('summary').click();
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
        assert.equal(await prop('lineReference').inputValue(),'normal');
        exported.model.loads[0].id='reversed';
        exported.model.nodes[1].x=-3;exported.model.nodes[1].y=-4;
        await open(exported.model,3);
        await picker.selectOption('load:reversed');
        const paths=await page.locator('#canvas [data-object="load"] [data-vector="force"] path[stroke]').evaluateAll(items=>items.map(item=>item.getAttribute('d')));
        const last=paths.at(-1).match(/[-+\d.e]+/g).map(Number);
        assert.ok(last[2]>last[0] && last[3]>last[1], 'Reversed member normal must point right and down');
        assert.match(await page.locator('#section-free-body-content').textContent(),/intensity along local/);
        assert.equal(await page.evaluate(()=>document.documentElement.scrollWidth),width);
        await prop('lineReference').scrollIntoViewIfNeeded();
        await page.screenshot({path:join(output,'line-'+width+'.png')});
        assert.deepEqual(errors,[]);
        await writeFile(join(output,'result-'+width+'.json'),JSON.stringify({width,point,exported,errors},null,2));
        await page.close();
    }
} finally {await browser.close();}
