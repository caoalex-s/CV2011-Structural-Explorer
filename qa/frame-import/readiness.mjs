/** Reproduce the lost-file race deterministically with the ordinary file picker.
 * Only the module response and File.text completion are held. The checker,
 * service worker, drawing UI, and inclined fixture are the normal ones.
 */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { copyFile, mkdir, readFile, writeFile } from 'node:fs/promises';
import { chromium } from '../../.data/student-tools/node_modules/playwright/index.mjs';

const origin = 'http://127.0.0.1:8765/';
const output = '.data/import-evidence';
await mkdir(output, {recursive:true});
const fixtureRoot = 'qa/inclined-frame/published-fixtures/cantilever-interior';
const {model, query} = JSON.parse(await readFile(fixtureRoot+'.request.json','utf8'));
const nativeReport = await readFile(fixtureRoot+'.report','utf8');
const browser = await chromium.launch();
const page = await browser.newPage();
const errors = [];
page.on('pageerror', error => errors.push(String(error)));
const evidence = {errors};
const file = (name, drawing) => ({name, mimeType:'application/json',
    buffer:Buffer.from(JSON.stringify({version:2,model:drawing}))});
const choose = file => page.locator('#model-file').setInputFiles(file);
const ready = () => page.waitForFunction(() => !document.querySelector('#workspace').inert);
const held = name => page.waitForFunction(name => typeof window.releaseFile?.[name] === 'function', name);
const release = name => page.evaluate(name => window.releaseFile[name](), name);

try {
    const moduleRequested = Promise.withResolvers();
    const moduleReady = Promise.withResolvers();
    await page.route(url => url.pathname.endsWith('/app.js'), async route => {
        moduleRequested.resolve();
        await moduleReady.promise;
        await route.continue();
    });
    await page.addInitScript(() => {
        const read = File.prototype.text;
        window.releaseFile = {};
        File.prototype.text = async function () {
            if (this.name.startsWith('hold-')) {
                await new Promise(resolve => { window.releaseFile[this.name] = resolve; });
            }
            return read.call(this);
        };
    });
    await page.goto(origin, {waitUntil:'commit'});
    await moduleRequested.promise;
    assert.equal(await page.locator('#workspace').evaluate(el => el.inert),true);
    await choose(file('hold-early.json',model));
    moduleReady.resolve();
    await held('hold-early.json');
    assert.equal(await page.locator('#frame-generate').isDisabled(),true);
    await page.locator('#frame-generate').evaluate(button => button.click());
    assert.equal(await page.evaluate(async () => (await navigator.serviceWorker.getRegistrations()).length),0);
    await release('hold-early.json');
    await ready();
    const active = await page.evaluate(() => JSON.parse(localStorage.getItem('cv2011-model')));
    assert.deepEqual(active.nodes,model.nodes);
    const geometry = await page.locator('#workspace-operation').innerText();
    assert.match(geometry,/B \(1, 2\)/);
    const path = await page.locator('[data-object="member"][data-id="AB"] path').first().getAttribute('d');
    const [x1,y1,x2,y2] = path.match(/-?[\d.]+/g).map(Number);
    assert.ok(x2>x1 && y2<y1);
    evidence.activeGeometry = {geometry,path};
    await page.locator('#frame-parameter').fill(String(query.parameter));
    await page.locator('#frame-side').selectOption(query.cutSide);
    await Promise.all([page.waitForNavigation(),page.locator('#frame-generate').click()]);
    await page.waitForFunction(() => {
        try { return JSON.parse(document.querySelector('#portal-certificate').textContent).protocol === 'CV2011_INCLINED_1'; }
        catch { return false; }
    },null,{timeout:190000});
    const receipt = JSON.parse(await page.locator('#portal-certificate').textContent());
    assert.deepEqual(receipt.sourceRequest.model.nodes,model.nodes);
    assert.deepEqual(receipt.sourceRequest.query,query);
    assert.equal(receipt.report,nativeReport);
    assert.equal(receipt.reportDigest,createHash('sha256').update(nativeReport).digest('hex'));
    evidence.receipt = receipt;
    await page.locator('#worked-panel').screenshot({path:output+'/inclined.png'});

    // A slow read cannot replace a newer drawing, even when both use AB.
    await choose(file('hold-older.json',model));
    await held('hold-older.json');
    assert.equal(await page.locator('#frame-generate').isDisabled(),true);
    const replacement = structuredClone(model);
    replacement.nodes[1].y = 3;
    await choose(file('replacement.json',replacement));
    await ready();
    await release('hold-older.json');
    await page.waitForFunction(() => document.querySelector('#workspace-operation').textContent.includes('replacement.json'));
    assert.deepEqual(await page.evaluate(() => JSON.parse(localStorage.getItem('cv2011-model')).nodes),replacement.nodes);
    await choose({name:'broken.json',mimeType:'application/json',buffer:Buffer.from('{')});
    await ready();
    assert.match(await page.locator('#workspace-operation').innerText(),/Could not open broken.json/);
    assert.deepEqual(await page.evaluate(() => JSON.parse(localStorage.getItem('cv2011-model')).nodes),replacement.nodes);
    await choose(file('replacement.json',model));
    await ready();
    assert.deepEqual(await page.evaluate(() => JSON.parse(localStorage.getItem('cv2011-model')).nodes),model.nodes);
    assert.deepEqual(errors,[]);
    // Repeat the release smoke itself in a fresh context, including cancellation,
    // changed-load checks, exported receipts, and service-worker cleanup.
    const fixtureDirectory = '.data/live-portal/inclined-native';
    await mkdir(fixtureDirectory,{recursive:true});
    for(const suffix of ['.request.json','.report']) {
        await copyFile(fixtureRoot+suffix,fixtureDirectory+'/cantilever-interior'+suffix);
    }
    const manifest = await readFile('public/portal-checker/bundle/manifest.json');
    const result = {
        artifact:JSON.parse(manifest).files['checker.wasm'],
        bundle:createHash('sha256').update(manifest).digest('hex'),
        cases:[],
    };
    const {runMainInclinedCases} = await import('../inclined-frame/main-browser-cases.mjs');
    const fresh = await browser.newContext({acceptDownloads:true});
    try {
        await runMainInclinedCases({page:await fresh.newPage(),context:fresh,output,
            origin:new URL(origin).origin,base:'/',result});
        evidence.releaseSmoke = result;
    } finally {
        await fresh.close();
    }
    evidence.passed = true;
} finally {
    await writeFile(output+'/import.json',JSON.stringify(evidence,null,2));
    await browser.close();
}
