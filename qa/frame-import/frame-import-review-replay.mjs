/** Independent regression replay for the imported inclined cantilever.
 * Pass a Playwright module URL, the site base URL, the published fixture
 * request and native report paths, and a fresh evidence directory.
 */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { join } from 'node:path';

const [playwright, base, fixturePath, reportPath, output] = process.argv.slice(2);
assert.ok(playwright && base && fixturePath && reportPath && output);
const request = JSON.parse(await readFile(fixturePath, 'utf8'));
const nativeReport = await readFile(reportPath, 'utf8');
const { chromium } = await import(playwright);
const browser = await chromium.launch({ headless: true });
const context = await browser.newContext({ viewport: { width: 1440, height: 1000 } });
const page = await context.newPage();
const errors = [], posts = [], evidence = {};
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
page.on('pageerror', error => errors.push(String(error)));
page.on('request', request => {
    if (request.method() === 'POST') posts.push(new URL(request.url()).pathname);
});
await mkdir(output, { recursive: true });

const workspace = page.locator('#workspace');
const operation = page.locator('#workspace-operation');
const opener = page.locator('#import-model');
const file = page.locator('#model-file');
const generate = page.locator('#frame-generate');
const certificate = page.locator('#portal-certificate');
const serialize = model => JSON.stringify({ version: 2, model });
const importText = (name, text) => file.setInputFiles({ name, mimeType: 'application/json', buffer: Buffer.from(text) });

/** Release a deliberately held async step even when an assertion fails. */
function gate() {
    let open;
    const pending = new Promise(resolve => { open = resolve; });
    return { pending, open };
}

async function waitForMemberSlope(slope) {
    await page.waitForFunction(value => {
        const paths = document.querySelectorAll('#canvas [data-object="member"] path.hit');
        if (paths.length !== 1) return false;
        const match = paths[0].getAttribute('d').match(/^M ([-.\d]+) ([-.\d]+) L ([-.\d]+) ([-.\d]+)$/);
        if (!match) return false;
        const [, ax, ay, bx, by] = match.map(Number);
        return Math.abs((ay - by) / (bx - ax) - value) < 1e-8;
    }, slope, { timeout: 15000 });
    assert.equal(await page.locator('#section-member').inputValue(), 'AB');
    return page.locator('#canvas [data-object="member"] path.hit').getAttribute('d');
}

async function waitForReceipt(model) {
    await page.waitForFunction(expected => {
        try {
            const value = JSON.parse(document.querySelector('#portal-certificate').textContent);
            return value.protocol === 'CV2011_INCLINED_1' &&
                JSON.stringify(value.sourceRequest.model.nodes) === JSON.stringify(expected);
        } catch {
            return false;
        }
    }, model.nodes, { timeout: 190000 });
    const receipt = JSON.parse(await certificate.textContent());
    assert.deepEqual(receipt.sourceRequest.model, model);
    assert.equal(digest(receipt.packet), receipt.packetDigest);
    assert.equal(digest(receipt.report), receipt.reportDigest);
    assert.equal(digest(JSON.stringify(receipt.sourceRequest)), receipt.inputDigest);
    return receipt;
}

try {
    // 1. Hold startup until after file selection, as in the original failure.
    const appResponse = gate(), appRequested = gate();
    await page.route('**/app.js', async route => {
        appRequested.open();
        await appResponse.pending;
        await route.continue();
    }, { times: 1 });
    await page.goto(base, { waitUntil: 'commit' });
    try {
        await appRequested.pending;
        assert.equal(await workspace.getAttribute('aria-busy'), 'true');
        assert.notEqual(await workspace.getAttribute('inert'), null);
        await importText('early-cantilever.json', serialize(request.model));
        assert.equal(await workspace.getAttribute('aria-busy'), 'true');
    } finally {
        appResponse.open();
    }
    const firstPath = await waitForMemberSlope(2);
    assert.equal(await workspace.getAttribute('aria-busy'), 'false');
    const opened = await operation.innerText();
    assert.match(opened, /Opened early-cantilever\.json\. AB: A \(0, 0\) to B \(1, 2\) m\./);
    evidence.delayedStartup = { geometry: firstPath, member: 'AB', opened };

    // 2. Activate from the actual imported slope, then bind all three hashes.
    await page.locator('#frame-parameter').fill(String(request.query.parameter));
    await page.locator('#frame-side').selectOption(request.query.cutSide);
    await generate.click();
    const initial = await waitForReceipt(request.model);
    assert.equal(initial.report, nativeReport);
    assert.deepEqual(initial.sourceRequest.query, request.query);
    evidence.inclinedReceipt = initial;
    await page.screenshot({ path: join(output, 'early-import-inclined.png'), fullPage: true });

    // 3. Start a second read with the same ID and different endpoint geometry.
    // Control the race from the file boundary while keeping UI and solver real.
    const changed = structuredClone(request.model);
    changed.nodes.find(node => node.id === 'B').y = 3;
    await page.evaluate(() => {
        const read = File.prototype.text;
        window.testImportReads = {};
        File.prototype.text = function () {
            if (!this.name.startsWith('held-')) return read.call(this);
            return new Promise(resolve => { window.testImportReads[this.name] = () => resolve(read.call(this)); });
        };
    });
    await importText('held-older.json', serialize(request.model));
    await page.waitForFunction(() => !!window.testImportReads['held-older.json']);
    assert.equal(await workspace.getAttribute('aria-busy'), 'true');
    assert.equal(await generate.isEnabled(), false);
    await importText('held-newer.json', serialize(changed));
    await page.waitForFunction(() => !!window.testImportReads['held-newer.json']);
    await page.evaluate(() => window.testImportReads['held-newer.json']());
    const latestPath = await waitForMemberSlope(3);
    const latestOpened = await operation.innerText();
    assert.match(latestOpened, /Opened held-newer\.json\. AB: A \(0, 0\) to B \(1, 3\) m\./);
    await page.evaluate(() => window.testImportReads['held-older.json']());
    await generate.click();
    const current = await waitForReceipt(changed);
    assert.notEqual(current.inputDigest, initial.inputDigest);
    assert.notEqual(current.reportDigest, initial.reportDigest);
    evidence.lastImportWins = { geometry: latestPath, opened: latestOpened, receipt: current };
    await page.screenshot({ path: join(output, 'same-id-new-geometry.png'), fullPage: true });

    // 4. Invalid JSON must leave the last committed member visible and usable.
    await importText('broken.json', '{');
    await operation.filter({ hasText: /Could not open broken\.json/i }).waitFor({ state: 'visible' });
    assert.equal(await waitForMemberSlope(3), latestPath);
    assert.equal(await opener.isEnabled(), true);
    await importText('recovered.json', serialize(request.model));
    await waitForMemberSlope(2);
    await generate.click();
    const recovered = await waitForReceipt(request.model);
    assert.equal(recovered.report, nativeReport);
    evidence.recovery = { reportDigest: recovered.reportDigest };
    assert.deepEqual(posts, []);
    assert.deepEqual(errors, []);
    await writeFile(join(output, 'frame-import-review.json'), JSON.stringify({ evidence, posts, errors }, null, 2));
} catch (error) {
    await page.screenshot({ path: join(output, 'failure.png'), fullPage: true }).catch(() => {});
    await writeFile(join(output, 'failure.json'), JSON.stringify({ error: String(error.stack ?? error), evidence, posts, errors }, null, 2));
    throw error;
} finally {
    await browser.close();
}
