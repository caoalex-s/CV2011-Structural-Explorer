/** End-to-end checks on a synthetic local pilot, including the isolation reload. */
import assert from 'node:assert/strict';
import { chromium } from '../../.data/student-tools/node_modules/playwright/index.mjs';
import { mkdir, writeFile } from 'node:fs/promises';

const browser = await chromium.launch();
const page = await browser.newPage();
const errors = [];
page.on('pageerror', error => errors.push(String(error)));
const report = { cases: [], errors };
try {
    await page.goto(process.argv[2]);
    await page.locator('#portal-exercise-link a').click();
    assert.equal(await page.locator('[data-object="member"]').count(), 0);
    assert.equal(await page.locator('#moment-reveal').isEnabled(), false);
    const model = await page.evaluate(async () => {
        const {example} = await import('./engine.js');
        const drawing = example('frame');
        Object.assign(drawing.loads[0], { fy:-6, qEnd:6 });
        return drawing;
    });
    async function loadDrawing() {
        await page.locator('#model-file').setInputFiles({
            name:'synthetic-portal.json', mimeType:'application/json', buffer:Buffer.from(JSON.stringify(model))
        });
        await page.waitForFunction(() => !document.querySelector('#moment-reveal').offsetParent ||
            document.querySelector('#moment-reveal').disabled);
    }
    async function submit(answer,expected) {
        await page.locator('#moment-prediction').fill(answer);
        await page.locator('#moment-check').click();
        await page.waitForFunction(text=>document.querySelector('#moment-feedback')?.textContent.includes(text),
            expected,{timeout:180000});
        report.cases.push({answer,feedback:await page.locator('#moment-feedback').innerText()});
    }
    await loadDrawing();
    await submit('1.337','Check the number');
    assert.equal(await page.locator('#checked-member-diagram').isVisible(),false);
    await submit('1.337,4.663','Correct for this drawing');
    await page.locator('#moment-reveal').click();
    assert.match(await page.locator('#moment-explanation').innerText(),/equal magnitude/);
    assert.equal(await page.locator('#checked-member-diagram').isVisible(),true);
    Object.assign(model.loads[0],{fy:-8,qEnd:8});
    await loadDrawing();
    await submit('1.337,4.663','Correct for this drawing');
    await page.locator('#moment-reveal').click();
    assert.match(await page.locator('#moment-explanation').innerText(),/4.0881/);
    model.loads[0].t = 0.25;
    await loadDrawing();
    await submit('1.337,4.663','Check the number');
    await page.locator('#moment-reveal').click();
    assert.match(await page.locator('#moment-explanation').innerText(),/largest magnitude occurs at/);
    await page.locator('[data-mode="insights"]').click();
    const events = page.locator('#insights-panel table').filter({has:page.getByText('Pseudonymous ID',{exact:true})});
    await events.getByText('DEMO-001').first().waitFor();
    report.events=await events.innerText();
    for (const label of ['first prediction','retry','reveal']) assert.ok(report.events.includes(label));
    assert.deepEqual(errors,[]);
} catch(error) {
    report.failure=String(error);
    report.feedback=await page.locator('#moment-feedback').textContent({timeout:1000}).catch(()=>null);
    report.checker=await page.locator('#portal-status').textContent({timeout:1000}).catch(()=>null);
    throw error;
} finally {
    await mkdir('.data/student-results',{recursive:true});
    await writeFile('.data/student-results/pilot-smoke.json',JSON.stringify(report,null,2));
    console.log(JSON.stringify(report));
    await browser.close();
}
