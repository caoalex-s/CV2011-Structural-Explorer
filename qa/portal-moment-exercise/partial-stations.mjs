/** Browser-level source-binding checks for the distributed-load stations that
 * previously exhausted the cardinal rational solver. Run against the built site. */
import { chromium } from '../../.data/student-tools/node_modules/playwright/index.mjs';
import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
const browser = await chromium.launch({ headless: true });
try {
    const page = await browser.newPage();
    await page.goto(process.argv[2]);
    await page.evaluate(async () => {
        await navigator.serviceWorker.register('./main-checker-sw.js');
        await navigator.serviceWorker.ready;
    });
    await page.reload();
    const results = await page.evaluate(async () => {
        const { PortalRuntime, sha256 } = await import('./portal-runtime.js');
        const { example } = await import('./engine.js');
        const { frameQueryConvention } = await import('./frame-candidate.js');
        const checker = new PortalRuntime(new URL('portal-checker/bundle/worker.mjs', location.href));
        const diagrams = new PortalRuntime(new URL('portal-checker/inclined-diagram/worker.mjs', location.href));
        const records = [];
        try {
            await Promise.all([checker.ready, diagrams.ready]);
            for (const [a,b] of [[1/6,5/6],[1/3,2/3],[0.175931752,0.83479184],[1/6,1]]) {
                const model = example('frame');
                Object.assign(model.loads[0],{t:a,end:b,fy:-8,qEnd:8});
                const query = {...frameQueryConvention,member:'BC',parameter:0.5,cutSide:'left'};
                const source = new TextEncoder().encode(JSON.stringify({model,query}));
                const started = performance.now();
                const base = await checker.checkFrame(source,'partial');
                const baseMilliseconds = Math.round(performance.now()-started);
                const diagram = base.state === 'accepted' ? await diagrams.checkDiagram(base.packet,true) : null;
                records.push({a,b,baseMilliseconds,totalMilliseconds:Math.round(performance.now()-started),state:base.state,message:base.message,diagram:diagram?.state,
                    sourceBound:base.inputDigest === await sha256(source),packetBound:!!diagram && diagram.inputDigest===base.packetDigest,
                    reportBound:!!diagram?.report && diagram.reportDigest===await sha256(diagram.report),
                    report:diagram?.report && new TextDecoder().decode(diagram.report)});
            }
        } finally { checker.dispose(); diagrams.dispose(); }
        return records;
    });
    await mkdir('.data/student-results',{recursive:true});
    await writeFile('.data/student-results/partial-stations.json',JSON.stringify(results,null,2));
    for(const r of results) { console.log(r.a,r.b,r.state,r.message,r.diagram); assert.equal(r.state,'accepted'); assert.equal(r.diagram,'accepted'); assert.ok(r.sourceBound && r.packetBound && r.reportBound); }
} finally { await browser.close(); }
