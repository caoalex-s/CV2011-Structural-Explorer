/** Independent blank-canvas replay. Pass a Playwright module URL, the base
 * site URL, a fresh evidence directory and "pilot" or "offline". The pilot
 * URL must be loopback and use a fresh synthetic account and database.
 */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { exactBrowserNumber, portalExerciseReference } from './portal-exercise-reference.mjs';
import { bounds, divide, enclosesReference, exact, multiply, subtract }
    from './member-diagram-inclined-reference.mjs';

const [playwrightModule, base, output, mode = 'offline'] = process.argv.slice(2);
assert.ok(playwrightModule && base && output, 'Pass the module URL, site URL and evidence directory');
assert.ok(['pilot', 'offline'].includes(mode));
if (mode === 'pilot') assert.ok(['localhost', '127.0.0.1'].includes(new URL(base).hostname));
const { chromium } = await import(playwrightModule);
const browser = await chromium.launch({ headless: true, ...(process.env.PORTAL_REPLAY_BROWSER ?
    { channel: process.env.PORTAL_REPLAY_BROWSER } : {}) });
const context = await browser.newContext({ viewport: { width: 1440, height: 1000 } });
const page = await context.newPage();
const errors = [], outgoingAttempts = [], records = [], safeguards = [];
const hash = value => createHash('sha256').update(value).digest('hex');
const momentPanel = page.locator('#portal-exercise');
const prediction = page.locator('#moment-prediction');
const reveal = page.locator('#moment-reveal');
const feedback = page.locator('#moment-feedback');
const diagram = page.locator('#checked-member-diagram');
const canvas = page.locator('#canvas');
const inspector = page.locator('#inspector');
const closeProperties = page.getByRole('button', { name: 'Close properties' });
const tool = name => page.locator(`button[data-tool="${name}"]`).click();
const loadInput = name => inspector.locator(`[data-property="${name}"]`);
const exerciseStep = 'portal_absolute_moment';
let canvasScale = 85;

page.on('pageerror', error => errors.push(String(error)));
page.on('request', request => {
    if (request.method() === 'POST' && new URL(request.url()).pathname === '/api/attempts') {
        outgoingAttempts.push(request.url());
    }
});
// An offline rehearsal may use a static development server on loopback.
if (mode === 'offline' && ['localhost', '127.0.0.1'].includes(new URL(base).hostname)) {
    await context.route('**/api/health', route => route.fulfill({ status: 503, json: { available: false } }));
}
await mkdir(output, { recursive: true });

async function waitForFeedback(expected) {
    await page.waitForFunction(({ text, flags }) =>
        new RegExp(text, flags).test(document.querySelector('#moment-feedback')?.textContent ?? '') ||
        /correct for|number and locations|ungraded|check the beam direction|enter one or more/i
            .test(document.querySelector('#moment-feedback')?.textContent ?? ''),
    { text: expected.source, flags: expected.flags }, { timeout: 330000 });
    assert.match(await feedback.innerText(), expected);
}

async function point(x, y, click = true) {
    assert.equal(await closeProperties.isVisible(), false, 'Close the inspector before placing objects');
    await canvas.scrollIntoViewIfNeeded();
    const target = await canvas.evaluate((svg, [x, y, scale]) => {
        const point = new DOMPoint(500 + (x - 4) * scale, 200 - y * scale).matrixTransform(svg.getScreenCTM());
        return { x: point.x, y: point.y, onCanvas: svg.contains(document.elementFromPoint(point.x, point.y)) };
    }, [x, y, canvasScale]);
    assert.ok(target.onCanvas, `Drawing point (${x}, ${y}) missed the canvas`);
    if (click) await page.mouse.click(target.x, target.y);
    else await page.mouse.move(target.x, target.y);
}

async function member(a, b) {
    await tool('member');
    await point(...a);
    await point(...b);
}

async function selectLoad() {
    if (await closeProperties.isVisible()) await closeProperties.click();
    await tool('select');
    await canvas.locator('[data-object="load"] text').click();
    await inspector.getByRole('heading', { name: 'Load properties' }).waitFor();
}

async function setNumber(property, value) {
    const input = loadInput(property);
    await input.fill(String(value));
    await input.press('Tab');
    assert.equal(Number(await input.inputValue()), Number(value));
}

function parseRational(value) {
    return value.split('/').map(BigInt);
}

function pointInterval(value) {
    return [parseRational(value), parseRational(value)];
}

function rationalNumber(value) {
    const [top, bottom] = value.split('/').map(Number);
    return top / bottom;
}

function compareRationals(left, right) {
    const [leftTop, leftBottom] = parseRational(left);
    const [rightTop, rightBottom] = parseRational(right);
    const crossDifference = leftTop * rightBottom - rightTop * leftBottom;
    return crossDifference < 0n ? -1 : Number(crossDifference > 0n);
}

/** Two signed enclosures can overlap after taking their absolute values.
 * Discard a candidate only when another lower bound exceeds its upper bound.
 */
function possibleAbsolutePeaks(rows) {
    const enclosures = rows.map(row => {
        const [yLow, yHigh] = row.m;
        const absoluteEndpoints = row.m.map(value => value.replace(/^-/, '')).sort(compareRationals);
        const containsZero = compareRationals(yLow, '0/1') <= 0 && compareRationals(yHigh, '0/1') >= 0;
        return { ...row, magnitude: [containsZero ? '0/1' : absoluteEndpoints[0], absoluteEndpoints[1]] };
    });
    return enclosures.filter(candidate =>
        !enclosures.some(other => compareRationals(other.magnitude[0], candidate.magnitude[1]) > 0));
}

function referenceForLoad([t, end, firstIntensity, lastIntensity]) {
    return portalExerciseReference({
        start: multiply(exact(6), exactBrowserNumber(t)),
        end: multiply(exact(6), exactBrowserNumber(end)),
        wStart: exactBrowserNumber(firstIntensity),
        wEnd: exactBrowserNumber(lastIntensity),
    });
}

function compareMomentRows(rows, expected) {
    assert.equal(rows.length, expected.candidates.length);
    const expectedMin = Math.min(...expected.candidates.map(row => rationalNumber(row.m[0])));
    const expectedMax = Math.max(...expected.candidates.map(row => rationalNumber(row.m[1])));
    for (const candidate of expected.candidates) {
        const side = candidate.side === 'stationary' ? 'interior' : candidate.side;
        const possible = rows.filter(row => Number(row.pieceIndex) === candidate.piece && row.side === side &&
            enclosesReference([row.xLow, row.xHigh], candidate.x));
        assert.equal(possible.length, 1, `Moment row at ${candidate.x.map(rationalNumber)} m`);
        const row = possible[0];
        assert.ok(enclosesReference([row.yLow, row.yHigh], candidate.m), 'Moment enclosure misses hand reference');
        assert.ok(rationalNumber(row.xHigh) - rationalNumber(row.xLow) < 1e-5, 'Station enclosure is too wide');
        assert.ok(rationalNumber(row.yHigh) - rationalNumber(row.yLow) < 1e-5, 'Moment enclosure is too wide');
        assert.equal(row.min, String(Math.abs(rationalNumber(candidate.m[0]) - expectedMin) < 1e-10));
        assert.equal(row.max, String(Math.abs(rationalNumber(candidate.m[1]) - expectedMax) < 1e-10));
    }
}

function compareCoefficients(rows, expected) {
    assert.equal(rows.length, expected.pieces.length);
    for (const [index, piece] of expected.pieces.entries()) {
        const row = rows[index];
        if ('start' in row) {
            assert.deepEqual([row.start, row.end], [piece.start[0], piece.end[0]]);
            for (const field of ['shear', 'moment']) {
                const coefficients = row[field].split(',').map(value => value.trim());
                for (const [power, coefficient] of piece[field].entries()) {
                    assert.equal(coefficients[power] ?? '0/1', coefficient[0]);
                }
            }
            continue;
        }
        const [start, end] = [pointInterval(piece.start[0]), pointInterval(piece.end[0])];
        const length = subtract(end, start);
        assert.equal(row.left, bounds(divide(start, exact(6)))[0]);
        assert.equal(row.right, bounds(divide(end, exact(6)))[0]);
        assert.equal(row.b, bounds(multiply(pointInterval(piece.shear[1][0]), length))[0]);
        assert.equal(row.c, bounds(multiply(pointInterval(piece.shear[2][0]), multiply(length, length)))[0]);
        assert.ok(enclosesReference([row.vLow, row.vHigh], piece.shear[0]));
        assert.ok(enclosesReference([row.mLow, row.mHigh], piece.moment[0]));
    }
}

async function check(answer, expected) {
    await prediction.fill(answer);
    await page.locator('#moment-check').click();
    await waitForFeedback(expected);
}

async function locked() {
    assert.equal(await diagram.isVisible(), false, 'The checked answer was visible before reveal');
    assert.equal(await page.locator('#section-results').isVisible(), false);
    assert.equal(await page.locator('#moment-explanation').textContent(), '');
}

async function readCheckedDrawing(expectedLoad) {
    const receipt = JSON.parse(await page.locator('#portal-certificate').textContent());
    const { sourceRequest, packet, diagram: certificate } = receipt;
    assert.equal(hash(JSON.stringify(sourceRequest)), receipt.inputDigest);
    assert.equal(hash(packet), certificate.packetDigest);
    assert.equal(hash(certificate.report), certificate.reportDigest);
    assert.equal(sourceRequest.query.member, await page.getByLabel('Inspect member').inputValue());
    const load = sourceRequest.model.loads[0];
    assert.equal(load.member, sourceRequest.query.member);
    assert.deepEqual([load.t, load.end, -load.fy, -load.qEnd], expectedLoad);
    const reference = referenceForLoad(expectedLoad);
    const datasets = locator => locator.evaluateAll(rows => rows.map(row => ({ ...row.dataset })));
    compareCoefficients(await datasets(diagram.locator('[data-piece]')), reference);
    const rows = await datasets(diagram.locator('[data-field="M"][data-candidate]'));
    compareMomentRows(rows, reference);
    const signedExtrema = rows.filter(row => row.min === 'true' || row.max === 'true').map(row =>
        ({ x: [row.xLow, row.xHigh], m: [row.yLow, row.yHigh], min: row.min === 'true', max: row.max === 'true' }));
    return { receipt, certificate, reference, signedExtrema };
}

async function collect(name, expectedLoad) {
    await reveal.click();
    await diagram.waitFor({ state: 'visible', timeout: 30000 });
    const { receipt, certificate, reference, signedExtrema } = await readCheckedDrawing(expectedLoad);
    const explanation = await page.locator('#moment-explanation').innerText();
    assert.match(explanation, /\bw\b/);
    assert.match(explanation, /\bV\b/);
    assert.match(explanation, /\bM\b/);
    assert.ok(records.every(record => record.inputDigest !== receipt.inputDigest));
    records.push({ name, load: expectedLoad, explanation, feedback: await feedback.innerText(),
        inputDigest: receipt.inputDigest, packetDigest: certificate.packetDigest,
        reportDigest: certificate.reportDigest, artifact: certificate.artifact,
        bundle: certificate.bundle, signedExtrema, reference });
    await page.screenshot({ path: join(output, `${name}.png`), fullPage: true });
    console.log(`Verified ${name}`);
}

async function editBoundaries(start, end) {
    await selectLoad();
    await setNumber('t', start);
    await setNumber('end', end);
    await locked();
    assert.equal(await prediction.inputValue(), '', 'An edited drawing retained a stale prediction');
}

async function replaceLoad() {
    await selectLoad();
    await page.getByRole('button', { name: 'Delete selected object' }).click();
    await tool('distributed');
}

async function visibleStation(x, expected) {
    await point(x, 2, false);
    assert.match(await page.locator('#tool-hint').innerText(), expected);
}

try {
    // 1. Discover the exercise and use the same canvas controls as a student.
    await page.goto(base);
    await page.getByRole('link', { name: 'Course', exact: true }).first().click();
    await page.getByRole('link', { name: 'Portal frame · maximum |M|', exact: true }).click();
    await momentPanel.waitFor({ state: 'visible' });
    assert.match(await momentPanel.getByRole('heading').textContent(), /largest \|M\|.*BC/);
    assert.equal(await canvas.locator('[data-object="member"]').count(), 0, 'Fresh exercise must open blank');
    const spacing = page.getByLabel('Grid spacing (m)');
    if (!(await spacing.isVisible())) await page.getByText('Snapping', { exact: true }).click();
    await page.getByLabel('Snap to grid and geometry').check();
    await spacing.fill('0.5');
    await spacing.press('Tab');
    await member([0, -2], [0, 2]);
    await member([0, 2], [6, 2]);
    await member([6, 2], [6, -2]);
    await tool('fixed');
    await point(0, -2);
    await point(6, -2);
    for (let step = 0; step < 2; step++) {
        await page.getByRole('button', { name: 'Zoom out' }).click();
        canvasScale /= 1.25;
    }
    await tool('distributed');
    await point(0.04, 2);
    await point(5.96, 2);
    await selectLoad();
    assert.equal(Number(await loadInput('t').inputValue()), 0);
    assert.equal(Number(await loadInput('end').inputValue()), 1);
    await setNumber('fy', 6);
    await setNumber('qEnd', -6);

    // 2. Require both tied peaks, preserve the reveal boundary, and retry.
    assert.ok(await reveal.isDisabled());
    await locked();
    await check('1.337', /number and locations|try again/i);
    await locked();
    await check('1.337, 4.663', /correct for this drawing/i);
    await locked();
    await collect('reference', [0, 1, 6, -6]);
    await check('4.663, 1.337', /correct for this drawing/i);

    // 3. Check an independent magnitude edit, then two different extents.
    await selectLoad();
    await setNumber('fy', 8);
    await setNumber('qEnd', -8);
    await locked();
    assert.equal(await prediction.inputValue(), '');
    await check('1.337, 4.663', /correct for this drawing/i);
    await collect('magnitude', [0, 1, 8, -8]);
    await editBoundaries(0.25, 0.75);
    await check('1.801, 4.199', /correct for this drawing/i);
    await collect('middle-half', [0.25, 0.75, 8, -8]);
    await editBoundaries(1/6, 1);
    await check('1.885, 5.115', /number and locations|try again/i);
    await locked();
    await check('1.885', /correct for this drawing/i);
    await collect('one-sided', [1/6, 1, 8, -8]);
    await replaceLoad();
    await visibleStation(3.02, /station 1\/2 of the span/);
    await visibleStation(1.02, /station 1\/6 of the span/);
    await point(1.02, 2);
    await visibleStation(4.98, /station 5\/6 of the span/);
    await point(4.98, 2);
    await selectLoad();
    assert.equal(Number(await loadInput('t').inputValue()), 1/6);
    assert.equal(Number(await loadInput('end').inputValue()), 5/6);
    await setNumber('fy', 8);
    await setNumber('qEnd', -8);
    await check('1.553, 4.447', /magnitudes unresolved/i);
    const nonDyadic = await readCheckedDrawing([1/6, 5/6, 8, -8]);
    assert.equal(possibleAbsolutePeaks(nonDyadic.signedExtrema).length, 2,
        'The non-dyadic control must leave overlapping absolute bounds');
    await collect('non-dyadic', [1/6, 5/6, 8, -8]);

    // 4. Verify the opt-in arithmetic-limit response and ordinary Undo.
    await editBoundaries(1e-200, 1);
    await check('1.337, 4.663', /limit|inconclusive|ungraded/i);
    await locked();
    const adjustment = page.locator('#moment-adjustment');
    await adjustment.getByRole('button', { name: /apply/i }).waitFor({ timeout: 30000 });
    assert.match(await adjustment.innerText(), /start/i);
    assert.match(await adjustment.innerText(), /1e-200/i);
    await selectLoad();
    assert.equal(Number(await loadInput('t').inputValue()), 1e-200, 'The checker changed the boundary without consent');
    await page.screenshot({ path: join(output, 'arithmetic-limit.png'), fullPage: true });
    await adjustment.getByRole('button', { name: /apply/i }).click();
    await selectLoad();
    assert.equal(Number(await loadInput('t').inputValue()), 0);
    await page.getByRole('button', { name: 'Undo', exact: true }).click();
    await selectLoad();
    assert.equal(Number(await loadInput('t').inputValue()), 1e-200);
    await locked();

    // 5. A pointer placement away from a magnetic station remains arbitrary.
    await replaceLoad();
    await point(1.24, 2);
    await point(4.26, 2);
    await selectLoad();
    const arbitraryStart = Number(await loadInput('t').inputValue());
    const arbitraryEnd = Number(await loadInput('end').inputValue());
    assert.ok(Math.abs(6 * arbitraryStart - 1.24) < 0.03, 'Arbitrary start was rounded away');
    assert.ok(Math.abs(6 * arbitraryEnd - 4.26) < 0.03, 'Arbitrary end was rounded away');
    const arbitrary = [arbitraryStart, arbitraryEnd, 8, -8];
    await setNumber('fy', 8);
    await setNumber('qEnd', -8);
    const absoluteExtrema = referenceForLoad(arbitrary).candidates.map(({ m, x }) =>
        ({ magnitude: Math.abs(rationalNumber(m[0])), position: rationalNumber(x[0]) }))
        .sort((a, b) => b.magnitude - a.magnitude);
    assert.ok(absoluteExtrema[0].magnitude - absoluteExtrema[1].magnitude > 0.01);
    await check(absoluteExtrema[0].position.toFixed(4), /correct for this drawing/i);
    await collect('arbitrary-pointer', arbitrary);

    // 6. Check near-symmetric source changes through the visible inspector.
    await editBoundaries(0, 1);
    await setNumber('fy', 6);
    await setNumber('qEnd', -6);
    await closeProperties.click();
    await tool('select');
    await canvas.locator('[data-object="node"] text').filter({ hasText: /^D$/ }).click();
    await inspector.getByRole('heading', { name: 'Node properties' }).waitFor();
    const elevatedFoot = -1.9999999999999998;
    assert.equal(2 - elevatedFoot, 4, 'Control must be indistinguishable under floating subtraction');
    await setNumber('y', elevatedFoot);
    await check('1.337, 4.663', /check the beam direction|unresolved/i);
    await locked();
    safeguards.push({ changed: 'right base elevation', value: elevatedFoot, feedback: await feedback.innerText() });
    await setNumber('y', -2);
    await closeProperties.click();
    await point(6, 0);
    await inspector.getByRole('heading', { name: 'Member properties' }).waitFor();
    const stifferColumn = 20000.000000000004;
    assert.notEqual(stifferColumn, 20000);
    await setNumber('EI', stifferColumn);
    await check('1.337, 4.663', /check the beam direction|unresolved/i);
    await locked();
    safeguards.push({ changed: 'right column EI', value: stifferColumn, feedback: await feedback.innerText() });
    await setNumber('EI', 20000);
    await selectLoad();
    const unequalIntensity = -5.999999999999999;
    await setNumber('qEnd', unequalIntensity);
    await check('1.337, 4.663', /magnitudes unresolved|number and locations/i);
    await locked();
    const twoLocationFeedback = await feedback.innerText();
    const unequal = await readCheckedDrawing([0, 1, 6, unequalIntensity]);
    const possibleCertified = possibleAbsolutePeaks(unequal.signedExtrema);
    const exactWinners = possibleAbsolutePeaks(unequal.reference.candidates);
    assert.equal(exactWinners.length, 1, 'Independent mechanics must separate the two absolute moments');
    const [winner] = exactWinners;
    const evidence = {
        changed: 'load intensity at C', value: unequalIntensity, exactValue: bounds(exactBrowserNumber(unequalIntensity))[0],
        twoLocationFeedback, signedExtrema: unequal.signedExtrema, possibleCertified, independentWinner: winner,
        sourceDigest: unequal.receipt.inputDigest, packetDigest: unequal.certificate.packetDigest,
        reportDigest: unequal.certificate.reportDigest,
    };
    if (possibleCertified.length === 1) {
        assert.match(twoLocationFeedback, /number and locations/i);
        assert.ok(enclosesReference(possibleCertified[0].x, winner.x), 'The certified winner must contain the independent station');
        const station = rationalNumber(winner.x[0]).toFixed(4);
        await check(station, /correct for this drawing/i);
        await locked();
        Object.assign(evidence, { station, singleLocationFeedback: await feedback.innerText() });
    } else {
        assert.equal(possibleCertified.length, 2);
        assert.match(twoLocationFeedback, /magnitudes unresolved/i);
    }
    safeguards.push(evidence);

    // 7. Distinguish first prediction, retry, reveal and assisted retry.
    await page.getByRole('button', { name: 'Learning insights' }).click();
    const table = page.locator('#insights-panel h2').filter({ hasText: 'Portal exercise predictions' }).locator('xpath=following-sibling::table[1]');
    await table.waitFor();
    if (mode === 'pilot') {
        await page.getByRole('heading', { name: /instructor view/i }).waitFor();
        await table.getByRole('cell', { name: 'DEMO-001', exact: true }).first().waitFor();
        assert.ok(outgoingAttempts.length > 0);
    } else {
        assert.equal(outgoingAttempts.length, 0, 'Offline predictions were submitted');
        await table.getByRole('cell', { name: 'local-unassigned', exact: true }).first().waitFor();
    }
    const insight = await table.locator('tbody tr').evaluateAll(rows => rows.map(row =>
        Array.from(row.cells, cell => cell.textContent.trim())));
    assert.deepEqual(insight.slice(0, 4).map(row => row.slice(1)), [
        ['first prediction', '1.337', 'No reveal recorded'],
        ['retry', '1.337, 4.663', 'No reveal recorded'],
        ['reveal', '1.337, 4.663', 'Worked solution shown'],
        ['retry', '4.663, 1.337', 'Worked solution shown'],
    ]);
    const stored = await page.evaluate(step => JSON.parse(localStorage.getItem('cv2011-attempts') ?? '[]')
        .filter(event => event.step === step)
        .map(({ courseId, event, synced, solutionRevealed, model }) =>
            ({ courseId, event, synced: !!synced, solutionRevealed, load: model.loads[0] })), exerciseStep);
    assert.ok(stored.length >= 4);
    if (mode === 'offline') assert.ok(stored.every(event => !event.synced));
    assert.deepEqual(errors, []);
    await page.screenshot({ path: join(output, 'instructor-or-local-insights.png'), fullPage: true });
    await writeFile(join(output, 'portal-exercise-replay.json'), JSON.stringify({ mode, records, safeguards, insight, stored, errors }, null, 2));
} catch (error) {
    await page.screenshot({ path: join(output, 'failure.png'), fullPage: true });
    await writeFile(join(output, 'failure.json'), JSON.stringify({ error: String(error.stack ?? error), records, errors }, null, 2));
    throw error;
} finally {
    await browser.close();
}
