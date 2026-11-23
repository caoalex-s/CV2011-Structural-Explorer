/** Independent browser checks for the shared member, station and cut-side controls. */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';

const [playwright, base, output] = process.argv.slice(2);
assert.ok(playwright && base && output);
const { chromium } = await import(playwright);
const browser = await chromium.launch();
const cases = [];
const hash = value => createHash('sha256').update(value).digest('hex');
await mkdir(output, { recursive:true });

const beam = {
    nodes:[{id:'A',x:0,y:0},{id:'B',x:8,y:0}],
    members:[{id:'AB',a:'A',b:'B',EA:2000000,EI:20000}],
    supports:[
        {id:'S1',member:'AB',t:0,kind:'pin',angle:90},
        {id:'S2',member:'AB',t:1,kind:'roller',angle:90}
    ],
    loads:[
        {id:'P1',member:'AB',kind:'force',t:0.5,end:1,fx:0,fy:-20,mz:0,qEnd:0},
        {id:'M1',member:'AB',kind:'moment',t:0.5,end:1,fx:0,fy:0,mz:16,qEnd:0}
    ]
};
const continuous = {
    nodes:[{id:'A',x:0,y:0},{id:'B',x:4,y:0},{id:'C',x:8,y:0}],
    members:[
        {id:'AB',a:'A',b:'B',EA:2000000,EI:20000},
        {id:'BC',a:'B',b:'C',EA:2000000,EI:20000}
    ],
    supports:[
        {id:'S1',member:'AB',t:0,kind:'pin',angle:90},
        {id:'S2',member:'BC',t:1,kind:'roller',angle:90}
    ],
    loads:[{id:'P1',member:'AB',kind:'force',t:1,end:1,fx:0,fy:-20,mz:0,qEnd:0}]
};
const asNumber = field => Number(field.numerator) / Number(field.denominator);
const normalize = text => text.replaceAll('−','-').replace(/\s+/g,' ').trim();

async function review(size, viewport) {
    const mobile = size === 'phone';
    const context = await browser.newContext({viewport,isMobile:mobile,hasTouch:mobile});
    const page = await context.newPage();
    const errors=[], posts=[];
    page.on('pageerror', error => errors.push(String(error)));
    page.on('request', request => {
        if (request.method()==='POST') posts.push(new URL(request.url()).pathname);
    });
    const section=page.locator('#section-member'), t=page.locator('#frame-parameter');
    const slider=page.locator('#section-position'), side=page.locator('#frame-side');
    const receipt=page.locator('#portal-certificate'), fbd=page.locator('#section-fbd');
    const reveal=page.locator('#frame-generate');
    const records=[];
    async function ready() {
        await page.waitForFunction(() => {
            const workspace = document.querySelector('#workspace');
            return workspace && !workspace.inert;
        });
    }
    async function matchesFigure(expected) {
        await fbd.waitFor({state:'visible'});
        assert.equal(await fbd.getAttribute('data-member'),expected.member);
        assert.equal(Number(await fbd.getAttribute('data-parameter')),expected.parameter);
        assert.equal(await fbd.getAttribute('data-side'),expected.cutSide);
        if (expected.loads) {
            const names=await fbd.locator('[data-load-id]').evaluateAll(elements=>elements.map(el=>el.dataset.loadId));
            assert.deepEqual(names.sort(),expected.loads.toSorted());
        }
    }
    async function verifyReadouts(expected) {
        const readouts=normalize(await page.locator('#section-results').innerText());
        assert.match(readouts,new RegExp('Shear force V.*?' + expected.shear + '\\s*kN','i'));
        assert.match(readouts,new RegExp('Bending moment M.*?' + expected.moment + '\\s*kN\\s*[·⋅]?\\s*m','i'));
        if (mobile) {
            const compact=page.locator('.cut-readout');
            const strip=normalize(await compact.innerText());
            const signed = value => (value < 0 ? '-' : '\\+?') + Math.abs(value);
            assert.match(strip,new RegExp('V = ' + signed(expected.shear) + '\\s*kN'));
            assert.match(strip,new RegExp('M = ' + signed(expected.moment) + '\\s*kN\\s*[·⋅]?\\s*m'));
            assert.ok(await compact.evaluate(element=>element.scrollWidth <= element.clientWidth));
            assert.equal(await page.evaluate(()=>document.documentElement.scrollWidth),viewport.width);
        }
        return readouts;
    }
    async function noStale(previous) {
        const value=(await receipt.textContent()).trim();
        if (value) assert.notEqual(JSON.parse(value).inputDigest,previous);
    }
    async function check(name, expected) {
        const readouts=await verifyReadouts(expected);
        await matchesFigure(expected);
        await reveal.click();
        await page.waitForFunction(({member,parameter,cutSide,force}) => {
            try {
                const entry=JSON.parse(document.querySelector('#portal-certificate').textContent);
                const {query,model}=entry.sourceRequest;
                return query.member===member && query.parameter===parameter && query.cutSide===cutSide &&
                    (force===undefined || model.loads.find(load=>load.kind==='force')?.fy===-force);
            } catch { return false; }
        },expected,{timeout:150000});
        const value=JSON.parse(await receipt.textContent());
        assert.equal(value.protocol,'CV2011_FRAME_1');
        assert.equal(value.inputDigest,hash(JSON.stringify(value.sourceRequest)));
        assert.equal(value.packetDigest,hash(value.packet));
        assert.deepEqual(value.values.readouts.slice(0,3).map(asNumber),[0,expected.shear,expected.moment]);
        assert.equal(await page.evaluate(()=>crossOriginIsolated),true);
        await page.locator('#frame-worked-output').waitFor({state:'visible'});
        await matchesFigure(expected);
        const record={name,expected,readouts,inputDigest:value.inputDigest,packetDigest:value.packetDigest};
        records.push(record);
        await page.screenshot({path:join(output,size+'-'+name+'.png'),fullPage:true});
        return value.inputDigest;
    }
    async function importDrawing(drawing) {
        const payload=Buffer.from(JSON.stringify({version:2,model:drawing}));
        await page.locator('#model-file').setInputFiles({name:'shared-cut-test.json',mimeType:'application/json',buffer:payload});
        await page.waitForFunction(expected => {
            const workspace=document.querySelector('#workspace');
            const data=JSON.parse(localStorage.getItem('cv2011-model') ?? '{}');
            const actions=loads=>loads?.map(({id, member, kind, t, fx, fy, mz})=>[id, member, kind, t, fx, fy, mz]);
            return !workspace.inert && JSON.stringify(data.members)===JSON.stringify(expected.members) &&
                JSON.stringify(actions(data.loads))===JSON.stringify(actions(expected.loads));
        },drawing);
    }

    try {
        await page.goto(new URL('#sandbox',base).href);
        await ready();
        await page.getByRole('link',{name:'Course',exact:true}).first().click();
        await page.locator('#beams').getByRole('link',{name:'Simple beams',exact:true}).click();
        await page.locator('#beam-cut').waitFor();
        assert.equal(new URL(page.url()).searchParams.get('exercise'),'simple-beams');
        await page.getByRole('link',{name:'Sandbox',exact:true}).click();
        await ready();
        assert.equal(await page.getByRole('button',{name:'Show worked solution',exact:true}).count(),1);
        assert.equal(await page.locator('#portal-activate').isVisible(),false);
        await slider.focus();
        await page.keyboard.press('Home');
        assert.equal(await t.inputValue(),'0');
        assert.equal(await side.inputValue(),'right');
        await verifyReadouts({shear:10,moment:0});
        await page.keyboard.press('End');
        assert.equal(await t.inputValue(),'1');
        assert.equal(await side.inputValue(),'left');
        await verifyReadouts({shear:-10,moment:0});

        await t.fill('0.5');
        await t.press('Tab');
        await side.selectOption('left');
        const left={member:'AB',parameter:0.5,cutSide:'left',force:20,shear:10,moment:40,loads:[]};
        const right={...left,cutSide:'right',shear:-10,loads:['P1']};
        let digest=await check('point-left',left);
        await side.selectOption('right');
        await noStale(digest);
        digest=await check('point-right',right);

        await page.locator('#drawing-object').selectOption('load:P1');
        const input=page.locator('#inspector [data-property="fy"]');
        await input.fill('-30');
        await input.press('Tab');
        await noStale(digest);
        digest=await check('edited-point-right',{...right,force:30,shear:-15,moment:60});
        await side.selectOption('left');
        await noStale(digest);
        await check('edited-point-left',{...left,force:30,shear:15,moment:60});

        await importDrawing(beam);
        await t.fill('0.5');
        await t.press('Tab');
        await side.selectOption('left');
        digest=await check('couple-left',{...left,shear:12,moment:48});
        await side.selectOption('right');
        await noStale(digest);
        digest=await check('couple-right',{...right,shear:-8,moment:32,loads:['P1','M1']});

        await importDrawing(continuous);
        await section.selectOption('AB');
        await t.fill('1');
        await t.press('Tab');
        assert.equal(await side.inputValue(),'left');
        await noStale(digest);
        digest=await check('member-end',{...left,parameter:1});
        await section.selectOption('BC');
        await t.fill('0');
        await t.press('Tab');
        assert.equal(await side.inputValue(),'right');
        await noStale(digest);
        await check('next-member-start',{...right,member:'BC',parameter:0,loads:[]});

        await page.locator('.drawing-utilities > summary').click();
        await page.getByRole('button',{name:'Learning insights',exact:true}).click();
        await page.locator('#insights-panel').waitFor({state:'visible'});
        assert.equal(new URL(page.url()).hash,'#insights');
        await page.goBack();
        await page.locator('#section-results').waitFor({state:'visible'});
        assert.equal(new URL(page.url()).hash,'#sandbox');
        assert.deepEqual(errors,[]);
        assert.deepEqual(posts,[]);
        cases.push({size,records,errors,posts});
    } catch(error) {
        await page.screenshot({path:join(output,size+'-failure.png'),fullPage:true}).catch(()=>{});
        cases.push({size,records,error:String(error.stack??error),errors,posts});
    } finally { await context.close(); }
}
try {
    await review('desktop',{width:1440,height:1000});
    await review('phone',{width:390,height:844});
    await writeFile(join(output,'shared-cut-review.json'),JSON.stringify(cases,null,2));
    assert.ok(cases.every(entry=>!entry.error));
} finally { await browser.close(); }
