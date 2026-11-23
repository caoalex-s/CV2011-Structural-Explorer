/** Independent student replay for the 8 m simply supported beam.
 * Usage: node script.mjs PLAYWRIGHT_MODULE_URL BASE_URL EVIDENCE_DIRECTORY [offline|pilot]
 */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { pointLoadReference } from './simple-beam-reference.mjs';

const [playwright, base, directory, mode = 'offline'] = process.argv.slice(2);
assert.ok(playwright && base && directory);
assert.ok(['offline','pilot'].includes(mode));
if (mode === 'pilot') assert.ok(['127.0.0.1','localhost'].includes(new URL(base).hostname));
const { chromium } = await import(playwright);
const browser = await chromium.launch();
const compact = mode === 'offline';
const context = await browser.newContext({
    viewport: compact ? {width:390,height:844} : {width:1440,height:1000}, hasTouch: compact, isMobile: compact
});
const page = await context.newPage();
const cases = [], errors = [], posts = [];
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
page.on('pageerror', error => errors.push(String(error)));
page.on('request', request => {
    if (request.method() === 'POST') posts.push(new URL(request.url()).pathname);
});
await mkdir(directory, { recursive: true });

const cut = page.locator('#beam-cut');
const load = page.locator('#beam-load');
const record = page.locator('#beam-record');
const reveal = page.locator('#beam-reveal');
const answer = page.locator('#beam-answer');
const receipt = page.locator('#beam-receipt');
const control = name => page.getByRole('button', { name, exact: true });

async function noCurrentReceipt() {
    if (await receipt.count()) assert.equal((await receipt.textContent()).trim(), '');
}

async function predict({ shear = 'drop', moment = 'same' } = {}) {
    await page.locator('#beam-predict-v').selectOption(shear);
    await page.locator('#beam-predict-m').selectOption(moment);
    await record.click();
    assert.equal(await reveal.isEnabled(), true);
}

async function collect(name, settings) {
    const expected = pointLoadReference(settings);
    await page.waitForFunction(({cut, force, limit}) => {
        try {
            const value = JSON.parse(document.querySelector('#beam-receipt').textContent);
            const {model, query} = value.sourceRequest;
            return model.loads[0].fy === -force && query.parameter === cut / 8 &&
                (cut !== 4 || query.cutSide === limit);
        } catch { return false; }
    }, {cut:expected.cut, force:expected.force, limit:expected.limit}, { timeout:150000 });
    assert.ok(await answer.isVisible());
    await page.locator('#beam-fbd').waitFor({state:'visible'});
    const checked = JSON.parse(await receipt.textContent());
    const {model, query} = checked.sourceRequest;
    assert.deepEqual(model.nodes.map(({x,y})=>[x,y]), [[0,0],[8,0]]);
    assert.equal(model.members.length, 1);
    assert.deepEqual(model.supports.map(({kind,t})=>[kind,t]), [['pin',0],['roller',1]]);
    assert.equal(model.supports[1].angle, 90);
    assert.equal(model.loads.length, 1);
    assert.equal(model.loads[0].kind, 'force');
    assert.equal(model.loads[0].fx, 0);
    assert.equal(model.loads[0].fy, -expected.force);
    assert.equal(model.loads[0].t, 0.5);
    assert.equal(query.parameter, expected.cut / 8);
    assert.equal(query.member, model.members[0].id);
    assert.equal(checked.inputDigest, hash(JSON.stringify(checked.sourceRequest)));
    assert.equal(checked.packetDigest, hash(checked.packet));
    assert.match(checked.artifact, /^[a-f0-9]{64}$/);
    assert.deepEqual(checked.values, {
        normal:expected.forces.N, shear:expected.forces.V, moment:expected.forces.M,
        Ay:expected.reactions.Ay, By:expected.reactions.By
    });
    assert.equal(await page.evaluate(() => window.crossOriginIsolated), true);
    if (compact) {
        assert.equal(await page.evaluate(() => document.documentElement.scrollWidth), 390);
    }
    const plotted = await page.locator('#beam-fbd').innerHTML();
    const explanation = (await answer.innerText()).replaceAll('−','-');
    assert.match(explanation,/kN/i);
    cases.push({name,settings,checked,plotted,explanation});
    await page.screenshot({path:join(directory,name+'.png'),fullPage:true});
}

try {
    await page.goto(new URL('#sandbox',base).href);
    const courseLink = page.getByRole('link',{name:/^Course$|^Learn$/}).first();
    await courseLink.click();
    await page.getByRole('link',{name:/Simple beams/}).click();
    await cut.waitFor();
    assert.equal(new URL(page.url()).searchParams.get('exercise'),'simple-beams');
    if (mode === 'pilot') {
        await control('Session').click();
        const connected = page.waitForResponse(response => new URL(response.url()).pathname === '/api/me' && response.ok());
        await page.locator('#save-settings').click();
        await connected;
        await page.getByText('Connected to the verifier.',{exact:true}).waitFor();
    }
    await page.locator('#beam-left-limit').click();
    assert.equal(await cut.inputValue(),'16');
    assert.equal(await reveal.isEnabled(),false);
    await noCurrentReceipt();

    await predict({shear:'rise'});
    await predict();
    await reveal.focus();
    await page.keyboard.press('Enter');
    await collect('left-limit',{limit:'left'});

    await cut.focus();
    await page.keyboard.press('ArrowRight');
    assert.equal(await cut.inputValue(),'17');
    await collect('right-limit',{limit:'right'});

    await page.keyboard.press('ArrowRight');
    assert.equal(await cut.inputValue(),'18');
    await collect('right-of-load',{cut:4.25,limit:'right'});

    await page.locator('#beam-left-limit').click();
    await cut.focus();
    await page.keyboard.press('ArrowLeft');
    assert.equal(await cut.inputValue(),'15');
    await collect('left-of-load',{cut:3.75,limit:'left'});

    await load.fill('30');
    await load.press('Tab');
    await noCurrentReceipt();
    assert.equal(await reveal.isEnabled(),false);
    assert.equal(await answer.isVisible(),false);
    await page.locator('#beam-right-limit').click();
    assert.equal(await cut.inputValue(),'17');
    await predict();
    await reveal.click();
    await collect('changed-load-right-limit',{force:30,limit:'right'});
    await page.locator('#beam-left-limit').click();
    await collect('changed-load-left-limit',{force:30,limit:'left'});

    await control('Local replay').click();
    const history = page.locator('#history');
    await history.waitFor({state:'visible'});
    const events = await history.locator('summary').allTextContents();
    assert.match(events[0],/first prediction/i);
    assert.match(events[1],/retry/i);
    assert.match(events[2],/reveal/i);
    assert.equal(events.filter(event=>/first prediction/i.test(event)).length,2);
    assert.equal(events.filter(event=>/reveal/i.test(event)).length,2);
    await page.screenshot({path:join(directory,'local-replay.png'),fullPage:true});

    await control('Learning insights').click();
    const insights = page.locator('#insights-panel');
    await insights.getByRole('heading',{name:mode==='pilot' ? /Instructor view/i : 'Records from this browser'}).waitFor();
    const title = insights.getByRole('heading',{name:/Simple beam predictions/i});
    const rows = await title.locator('xpath=following-sibling::table[1]').locator('tbody tr').evaluateAll(elements =>
        elements.map(row=>Array.from(row.cells,cell=>cell.textContent.trim())));
    assert.equal(rows.length,events.length);
    assert.ok(rows.every(row=>row[0]===(mode==='pilot' ? 'DEMO-001':'local-unassigned')));
    assert.deepEqual(posts,mode==='pilot' ? events.map(()=>'/api/attempts') : []);
    assert.deepEqual(errors,[]);
    await page.screenshot({path:join(directory,'learning-insights.png'),fullPage:true});
    await writeFile(join(directory,'simple-beam-replay.json'),JSON.stringify({mode,cases,events,rows,posts,errors},null,2));
} catch (error) {
    await page.screenshot({path:join(directory,'failure.png'),fullPage:true}).catch(()=>{});
    await writeFile(join(directory,'failure.json'),JSON.stringify({error:String(error.stack ?? error),cases,posts,errors},null,2));
    throw error;
} finally {
    await browser.close();
}
