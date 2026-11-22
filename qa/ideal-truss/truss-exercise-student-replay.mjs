/** Independent Chromium replay of the ideal truss exercise. Pass a
 * Playwright module URL, development site URL and evidence directory.
 * Any predictions are synthetic, and the browser starts with empty storage.
 */
import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { rectangleTrussReference } from './truss-exercise-reference.mjs';

const [playwright, base, directory] = process.argv.slice(2);
assert.ok(playwright && base && directory, 'Provide Playwright, site and evidence directory');
const { chromium } = await import(playwright);
const browser = await chromium.launch({ headless: true });
const context = await browser.newContext({ viewport: { width: 1440, height: 1000 } });
const page = await context.newPage();
const errors = [], records = [], networkPosts = [];
page.on('pageerror', error => errors.push(String(error)));
page.on('request', request => {
    if (request.method() === 'POST') networkPosts.push(new URL(request.url()).pathname);
});
await mkdir(directory, { recursive: true });

const canvas = page.locator('#truss-canvas');
const response = page.locator('#response');
const reveal = page.locator('#reveal');
const tool = mode => page.locator('#truss-tool').selectOption(mode);
const control = name => page.getByRole('button', { name, exact: true });
const jointEdit = page.locator('#joint-edit');
const names = ['AB', 'BC', 'CD', 'DA', 'AC'];

async function moveToSvg(x, y) {
    await canvas.scrollIntoViewIfNeeded();
    const screenPoint = await canvas.evaluate((svg, [x, y]) => {
        const point = new DOMPoint(x, y).matrixTransform(svg.getScreenCTM());
        return { x: point.x, y: point.y, inside: svg.contains(document.elementFromPoint(point.x, point.y)) };
    }, [x, y]);
    assert.ok(screenPoint.inside, 'The visible SVG does not contain the intended click');
    await page.mouse.click(screenPoint.x, screenPoint.y);
}

async function chooseJoint(joint) {
    await page.locator('#choose').selectOption(joint);
}

async function editJoint(joint, changes) {
    await chooseJoint(joint);
    for (const [field, value] of Object.entries(changes)) {
        const input = jointEdit.locator(`[name="${field}"]`);
        if (field === 'support') await input.selectOption(value);
        else await input.fill(String(value));
    }
    await control('Apply joint edits').click();
}

async function connect(first, last) {
    await tool('bar');
    await canvas.locator(`[data-node="${first}"]`).click();
    await canvas.locator(`[data-node="${last}"]`).click();
}

async function locked() {
    assert.equal(await response.isVisible(), false, 'The prior calculation remained visible');
    assert.equal(await reveal.isEnabled(), false, 'An edit allowed reveal without a new prediction');
}

async function predict(expected, motion, { correction = false, alreadyRevealed = false } = {}) {
    const form = page.locator('#prediction');
    const state = expected.mechanismCount ? 'Mechanism' :
        expected.selfStressCount ? 'Stable and indeterminate' : 'Stable and determinate';
    await form.locator('[name="ideal"]').selectOption({ label: 'Two-force member' });
    await form.locator('[name="count"]').fill(String(expected.countDifference + (correction ? 1 : 0)));
    await form.locator('[name="state"]').selectOption({ label: state });
    await form.locator('[name="motion"]').fill(motion);
    await control('Record prediction').click();
    const feedback = await page.locator('#feedback').innerText();
    assert.match(feedback, /Idealisation correct/i);
    assert.match(feedback, /Stability prediction correct/i);
    assert.match(feedback, correction ? /Recount/i : /Count correct/i);
    assert.equal(await response.isVisible(), alreadyRevealed);
    return feedback;
}

function number(rational) {
    const [numerator, denominator = 1] = rational.split('/').map(Number);
    return numerator / denominator;
}

async function collect(name, reference) {
    await reveal.click();
    await response.waitFor({ state: 'visible' });
    const explanation = await response.innerText();
    assert.match(explanation, new RegExp(`rank\\s+${reference.equilibriumRank}\\b`, 'i'));
    assert.match(explanation, new RegExp(`${reference.mechanismCount} independent permitted motion`, 'i'));
    assert.match(explanation, new RegExp(`${reference.selfStressCount} independent self-equilibrated force system`, 'i'));
    const rows = await response.locator('table tbody tr').evaluateAll(elements =>
        elements.map(row => [...row.cells].map(cell => cell.textContent.trim())));
    if (Object.keys(reference.forces).length) {
        const expected = { ...reference.forces, ...reference.reactions };
        assert.equal(rows.length, Object.keys(expected).length);
        for (const [id, printed, sense] of rows) {
            const name = id === 'AD' ? 'DA' : id;
            assert.ok(Object.hasOwn(expected, name), `Unexpected action ${id}`);
            const expectedValue = number(expected[name]);
            assert.equal(Number(printed), expectedValue, `${id} signed force`);
            if (names.includes(name)) assert.equal(sense, expectedValue > 0 ? 'Tension' : expectedValue < 0 ? 'Compression' : 'Zero');
        }
        assert.equal(await response.locator('svg[aria-label^="Joint "][aria-label$=" free body"]').count(), 4);
        assert.match(explanation, /Method of joints/i);
        assert.match(explanation, /4B.\s*−\s*3P/i);
    } else {
        assert.equal(rows.length, 0, 'An unstable or underdetermined model presented unique member forces');
        if (reference.equilibriumExists) assert.match(explanation, /undetermined|indeterminate/i);
        else assert.match(explanation, /Static equilibrium is impossible/i);
    }
    const renderedProof = response.locator('#proof-scope');
    if (reference.bars <= 5) assert.equal(await renderedProof.isVisible(), true, name);
    const proof = await renderedProof.count() ? await renderedProof.innerText() : '';
    records.push({ name, reference, explanation, rows, proof });
    await page.screenshot({ path: join(directory, name + '.png'), fullPage: true });
    console.log('Verified ' + name);
}

try {
    // 1. Find the exercise through the main workspace and draw all bars.
    await page.goto(new URL('#sandbox', base).href);
    await page.getByRole('link', { name: /Ideal planar truss/i }).click();
    await canvas.waitFor({ state: 'visible' });
    await control('Blank drawing').click();
    await locked();
    assert.equal(await canvas.locator('[data-node]').count(), 0);
    await tool('joint');
    const bottom = 285, top = 65, left = 80, right = 80 + 4 * 220 / 3;
    for (const [x, y] of [[left, bottom], [right, bottom], [right, top], [left, top]]) await moveToSvg(x, y);
    for (const bar of names) await connect(...bar);
    assert.equal(await canvas.locator('[data-edge]').count(), 5);
    await editJoint('A', { support: 'pin' });
    await editJoint('B', { support: 'roller', rx: 0, ry: 1 });
    await editJoint('C', { fx: 12, fy: 0 });
    await locked();

    // 2. Try a wrong count, then retry and reveal the stable drawing.
    const stable = rectangleTrussReference();
    await predict(stable, 'No permitted infinitesimal motion.', { correction: true });
    await predict(stable, 'No permitted infinitesimal motion.');
    await collect('drawn-braced', stable);
    await predict(stable, 'No permitted infinitesimal motion.', { alreadyRevealed: true });
    await editJoint('C', { fx: -7 });
    await locked();
    const reversed = rectangleTrussReference({ load: -7 });
    await predict(reversed, 'No permitted infinitesimal motion.');
    await collect('reversed-load', reversed);
    await editJoint('C', { fx: 12 });

    // 3. Same number of joints; different rank and different mechanism.
    await control('Remove AC').click();
    await locked();
    const unbraced = rectangleTrussReference({ brace: false });
    await predict(unbraced, 'The upper edge can move horizontally while A and B remain fixed.');
    await collect('unbraced', unbraced);
    await control('Add AC').click();
    await control('Rotate roller B').click();
    await locked();
    const horizontal = rectangleTrussReference({ roller: 'horizontal' });
    await predict(horizontal, 'Rigid rotation about A.');
    await collect('concurrent-reactions', horizontal);

    // 4. Rejected edits leave the current drawing and its evidence intact.
    await editJoint('B', { rx: 0, ry: 0 });
    assert.match(await page.locator('#hint').innerText(), /nonzero roller reaction direction/i);
    await chooseJoint('A');
    await chooseJoint('B');
    assert.equal(await jointEdit.locator('[name="rx"]').inputValue(), '1');
    await editJoint('A', { x: 4 });
    assert.match(await page.locator('#hint').innerText(), /distinct.*position/i);
    await chooseJoint('B');
    await chooseJoint('A');
    assert.equal(await jointEdit.locator('[name="x"]').inputValue(), '0');

    // 5. Equilibrium existence and uniqueness are distinct from stability.
    await editJoint('C', { fx: 0 });
    await locked();
    const compatible = rectangleTrussReference({ roller: 'horizontal', load: 0 });
    await predict(compatible, 'Rigid rotation about A is still permitted.');
    await collect('compatible-mechanism', compatible);
    await control('Rotate roller B').click();
    await editJoint('C', { fx: 12 });
    await connect('B', 'D');
    assert.equal(await canvas.locator('[data-node]').count(), 4, 'Crossing bars gained an unintended joint');
    await locked();
    const redundant = rectangleTrussReference({ redundant: true });
    await predict(redundant, 'No permitted infinitesimal motion.');
    await collect('redundant', redundant);

    // 6. Examine the synthetic local sequence and check the legacy route.
    await control('Local replay').click();
    const history = page.locator('#history');
    await history.waitFor({ state: 'visible' });
    const events = await history.locator('summary').allTextContents();
    assert.match(events[0], /first prediction/i);
    assert.match(events[1], /retry/i);
    assert.match(events[2], /reveal/i);
    assert.match(events[3], /assisted retry/i);
    assert.deepEqual(networkPosts, []);
    await page.screenshot({ path: join(directory, 'local-replay.png'), fullPage: true });
    await page.getByRole('link', { name: 'Frame workspace', exact: true }).click();
    await page.getByRole('button', { name: 'Generate worked solution', exact: true }).waitFor();
    assert.equal(await canvas.count(), 0);
    assert.deepEqual(errors, []);
    await writeFile(join(directory, 'truss-exercise-replay.json'), JSON.stringify({ records, events, networkPosts, errors }, null, 2));
} catch (error) {
    await page.screenshot({ path: join(directory, 'failure.png'), fullPage: true });
    await writeFile(join(directory, 'failure.json'), JSON.stringify({ error: String(error.stack ?? error), records, errors }, null, 2));
    throw error;
} finally {
    await browser.close();
}
