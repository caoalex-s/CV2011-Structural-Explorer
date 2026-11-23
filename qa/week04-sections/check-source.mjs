/** Send edited source packets through the compiled browser checker. Only
 * synthetic fixtures are used, and the fixture server must be loopback. */
import assert from 'node:assert/strict';
import { writeFile } from 'node:fs/promises';
import { chromium } from '../../.data/student-tools/node_modules/playwright/index.mjs';

const url = new URL(process.argv[2]);
assert.equal(url.hostname, '127.0.0.1');
const browser = await chromium.launch();
try {
    const page = await browser.newPage();
    url.searchParams.set('exercise','week04-truss-sections');
    await page.goto(url.href);
    await page.locator('#section-drawing').waitFor();
    await page.evaluate(async () => {
        const { isolateForCheck } = await import('./truss-check.js');
        await isolateForCheck();
    });
    await page.reload();
    assert.ok(await page.evaluate(() => crossOriginIsolated));
    const cases = await page.evaluate(async () => {
        const { PortalRuntime } = await import('./portal-runtime.js');
        const fixture = await (await fetch('./week04-section-truss.json')).json();
        const { sectionPacket } = await import('./week04-section.js');
        const runtime = new PortalRuntime(new URL('./portal-checker/week04-section/worker.mjs',location.href));
        await runtime.ready;
        const results = {};
        const mutations = {
            original: () => {},
            roller: d => { d.joints[6].ry = 1; },
            otherGeometry: d => { d.joints[1].x = 1; },
            duplicate: d => { d.bars[1] = ['B','A']; },
            unknownJoint: d => { d.bars[0][0] = 'Z'; },
            extraLoad: d => { d.joints[1].fy = -1; },
            offTarget: (d,q) => { q.cut = 1; },
        };
        for (const [name, edit] of Object.entries(mutations)) {
            const drawing = structuredClone(fixture);
            const query = {side:'left',centre:'G',cut:3};
            edit(drawing,query);
            const result = await runtime.checkDiagram(sectionPacket(drawing,query),true);
            results[name] = {state:result.state, report:result.report instanceof Uint8Array};
        }
        runtime.dispose();
        return results;
    });
    assert.deepEqual(cases.original,{state:'accepted',report:true});
    for (const [name, value] of Object.entries(cases)) {
        if (name === 'original') continue;
        assert.equal(value.state,'inconclusive',name);
        assert.equal(value.report,false,name);
    }
    await writeFile('.data/student-results/offline/checker-source.json',JSON.stringify(cases,null,2));
} finally {
    await browser.close();
}
