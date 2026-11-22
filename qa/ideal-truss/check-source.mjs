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
    url.searchParams.set('exercise','ideal-planar-truss');
    await page.goto(url.href);
    await page.locator('#truss-canvas').waitFor();
    await page.evaluate(async () => {
        const { isolateForCheck } = await import('./truss-check.js');
        await isolateForCheck();
    });
    await page.reload();
    assert.ok(await page.evaluate(() => crossOriginIsolated));
    const cases = await page.evaluate(async () => {
        const { PortalRuntime } = await import('./portal-runtime.js');
        const { rectangle } = await import('./ideal-truss.js');
        const { packet } = await import('./truss-check.js');
        const runtime = new PortalRuntime(new URL('./portal-checker/ideal-truss/worker.mjs',location.href));
        await runtime.ready;
        const results = {};
        const mutations = {
            original: () => {},
            zeroRoller: d => { d.joints[1].ry = 0; },
            coincident: d => { d.joints[1].x = 0; },
            duplicate: d => { d.bars.push(['C','A']); },
            unknownJoint: d => { d.bars[0][0] = 'Z'; },
            selfBar: d => { d.bars[0][1] = 'A'; },
        };
        for (const [name, edit] of Object.entries(mutations)) {
            const drawing = rectangle();
            edit(drawing);
            const result = await runtime.checkDiagram(packet(drawing),true);
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
