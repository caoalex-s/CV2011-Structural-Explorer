/** Independent isolated Chromium replay of Week 04 Example 1. */
import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { performance } from 'node:perf_hooks';
import { sectionReference } from './section-truss-reference.mjs';
import { expectedSectionPackets, sha } from './section-truss-receipt-reference.mjs';

const [playwright, base, directory, mode = 'offline'] = process.argv.slice(2);
assert.ok(playwright && base && directory, 'Provide Playwright, site and evidence directory');
assert.ok(['offline', 'pilot'].includes(mode));
if (mode === 'pilot') assert.ok(['localhost', '127.0.0.1'].includes(new URL(base).hostname));
const { chromium } = await import(playwright);
const browser = await chromium.launch();
const context = await browser.newContext({ viewport: { width: 1440, height: 1000 } });
const page = await context.newPage();
const records = [], errors = [], networkPosts = [];
page.on('pageerror', error => errors.push(String(error)));
page.on('request', request => {
    if (request.method() === 'POST') networkPosts.push(new URL(request.url()).pathname);
});
await mkdir(directory, { recursive: true });

const cut = page.locator('#section-cut');
const side = page.locator('#section-side');
const centre = page.locator('#section-centre');
const load = page.locator('#section-load');
const record = page.locator('#record-section');
const reveal = page.locator('#reveal-section');
const response = page.locator('#section-response');
const receiptElement = page.locator('#section-receipt');
const control = name => page.getByRole('button', { name, exact: true });

async function select(element, value) {
    if (await element.evaluate(node => node.tagName === 'SELECT')) {
        await element.selectOption(String(value));
    } else {
        await element.fill(String(value));
        await element.press('Tab');
    }
}

async function noOldReceipt() {
    const previous = await receiptElement.count() ? await receiptElement.textContent() : '';
    assert.equal(previous.trim(), '', 'An edit left the previous checked receipt available');
    assert.equal(await reveal.isEnabled(), false, 'Reveal accepts a stale prediction');
    assert.equal(await response.isVisible(), false, 'An edit left the previous worked answer visible');
}

async function predict(forces, wrong = false) {
    for (const [index, force] of forces.entries()) {
        const prediction = wrong && index === 0 ? (force.state === 'C' ? 'T' : 'C') : force.state;
        await page.locator('#predict-' + force.member).selectOption(prediction);
    }
    await record.click();
    assert.equal(await reveal.isEnabled(), true);
}

function expectedExpression(rows, column, substituted) {
    const terms = rows.filter(row => row[column] !== 0);
    return terms.map((row, i) => {
        const [name, , , , radicand, component] = row;
        const value = row[column];
        const sign = value < 0 ? '−' : i === 0 ? '' : ' + ';
        const coefficient = column === 3 ? '(' + Math.abs(value) + ' m)' :
            Math.abs(value) === 1 ? '' : String(Math.abs(value));
        let force = name.length === 2 && name === name.toUpperCase() ? 'F' + name : name;
        if (substituted) {
            const magnitude = Math.abs(component);
            const decimal = radicand === 1 || !magnitude ? String(magnitude) :
                (magnitude === 1 ? '' : magnitude) + '√' + radicand;
            force = '(' + (component < 0 ? '−' : '') + decimal + ' kN)';
        }
        return sign + coefficient + force + (radicand === 1 ? '' : '/√' + radicand);
    }).join(' ');
}

async function collect(name, settings, { wrongFirst = false } = {}) {
    const expected = expectedSectionPackets(settings);
    if (wrongFirst) await predict(expected.reference.forces, true);
    await predict(expected.reference.forces);
    const began = performance.now();
    await reveal.click();
    await page.waitForFunction(digest => {
        const evidence = document.querySelector('#section-receipt');
        try { return JSON.parse(evidence.textContent).inputDigest === digest; }
        catch { return false; }
    }, sha(expected.packet), { timeout: 150000 });
    const wallMs = performance.now() - began;
    const receipt = JSON.parse(await receiptElement.textContent());
    assert.deepEqual(receipt.source, expected.source, 'Checked source differs from the lecture drawing');
    const { cut, side, centre } = expected.reference;
    assert.deepEqual(receipt.query, { cut, side, centre });
    assert.equal(receipt.report, expected.report, 'Report differs from independent equilibrium');
    assert.equal(receipt.reportDigest, sha(expected.report));
    assert.match(receipt.artifact, /^[a-f0-9]{64}$/);
    assert.ok(Number.isFinite(receipt.elapsedMs) && receipt.elapsedMs > 0);
    assert.equal(await page.evaluate(() => window.crossOriginIsolated), true);
    const terms = await response.locator('[data-term]').evaluateAll(rows => rows.map(row =>
        [row.dataset.term, ...['x','y','moment','radicand','component'].map(key => Number(row.dataset[key]))]
    ));
    const expectedTerms = expected.report.split('\n').slice(2, -4).map(line => {
        const [force, ...values] = line.split(',');
        return [force, ...values.map(Number)];
    });
    assert.deepEqual(terms, expectedTerms, 'The browser rendered different equation coefficients');
    for (const [column, axis] of ['x', 'y', 'moment'].entries()) {
        const equation = response.locator('[data-equation="' + axis + '"] p');
        const symbolicName = axis === 'moment' ? 'ΣM' + centre : 'ΣF' + axis;
        const forceUnits = axis === 'moment' ? 'kN·m' : 'kN';
        assert.deepEqual(await equation.allTextContents(), [
            symbolicName + ' = ' + expectedExpression(expectedTerms, column + 1, false) + ' = 0',
            expectedExpression(expectedTerms, column + 1, true) + ' = 0 ' + forceUnits
        ]);
    }
    const forces = await response.locator('[data-member]').evaluateAll(rows => rows.map(row => ({
        member: row.dataset.member,
        value: Number(row.dataset.component) * Math.sqrt(Number(row.dataset.radicand)),
        state: row.dataset.sense,
        text: row.textContent
    })));
    assert.deepEqual(forces.map(({ member, value, state }) => ({ member, value, state })),
        expected.reference.forces.map(({ member, value, state }) => ({ member, value, state })));
    for (const force of forces) {
        assert.match(force.text, force.state === 'T' ? /tension/i : force.state === 'C' ? /compression/i : /zero force/i);
    }
    assert.equal(terms.length, expected.reference.cutActions.length + expected.reference.external.length);
    assert.equal(forces.length, expected.reference.forces.length);
    const text = (await response.innerText()).replaceAll('−', '-');
    assert.match(text, /kN/);
    assert.match(text, /kN\s*[·⋅.]\s*m/);
    const arrows = await page.locator('#section-fbd [data-action]').evaluateAll(nodes => nodes.map(node => {
        const shaft = node.querySelector('line');
        const read = key => Number(shaft.getAttribute(key));
        return {
            name: node.dataset.action,
            direction: [Number(node.dataset.directionX), Number(node.dataset.directionY)],
            plottedDirection: [read('x2') - read('x1'), read('y1') - read('y2')]
        };
    }));
    for (const arrow of arrows) {
        assert.deepEqual(arrow.plottedDirection.map(Math.sign), arrow.direction.map(Math.sign),
            'The plotted arrow disagrees with its force direction');
    }
    const arrowFor = name => arrows.find(arrow => arrow.name === name);
    for (const action of expected.reference.cutActions) {
        const actual = arrowFor(action.member)?.direction;
        assert.ok(actual && actual.some(Boolean), `Missing cut arrow ${action.member}`);
        for (const [i, direction] of action.direction.entries()) {
            assert.equal(Math.sign(actual[i]), Math.sign(direction), `Incorrect cut arrow ${action.member}`);
        }
        assert.equal(actual[0] * action.direction[1] - actual[1] * action.direction[0], 0);
    }
    for (const action of expected.reference.external) {
        const actual = arrowFor(action.name)?.direction;
        if (action.force.every(value => value === 0)) {
            assert.equal(actual, undefined, `Unexpected arrow for zero ${action.name}`);
        } else {
            assert.deepEqual(actual?.map(Math.sign), action.force.map(Math.sign), `Incorrect external arrow ${action.name}`);
        }
    }
    records.push({ name, settings, wallMs, terms, forces, arrows, receipt });
    await page.screenshot({ path: join(directory, name + '.png'), fullPage: true });
    console.log('Verified ' + name + ' in ' + Math.round(wallMs) + ' ms');
}

try {
    await page.goto(new URL('#sandbox', base).href);
    await page.getByRole('link', { name: /Week 04.*section|Truss.*section/i }).click();
    await cut.waitFor();
    assert.equal(new URL(page.url()).searchParams.get('exercise'), 'week04-truss-sections');
    if (mode === 'pilot') {
        await control('Session').click();
        const connected = page.waitForResponse(result => new URL(result.url()).pathname === '/api/me' && result.ok());
        await page.locator('#save-settings').click();
        await connected;
        await page.getByText('Connected to the verifier.', { exact: true }).waitFor();
    }
    await select(cut, 1);
    await noOldReceipt();
    const offTarget = sectionReference({ cut: 1 });
    assert.match(await page.locator('#section-selection').innerText(),
        new RegExp(offTarget.cutActions.map(action => action.member).join(', ')));
    assert.equal(await record.isEnabled(), false);
    await select(cut, 5);
    await noOldReceipt();
    const farCut = sectionReference({ cut: 5 });
    assert.match(await page.locator('#section-selection').innerText(),
        new RegExp(farCut.cutActions.map(action => action.member).join(', ')));
    assert.equal(await record.isEnabled(), false);
    await select(cut, 3);
    await select(side, 'left');
    await select(centre, 'G');
    await collect('left-reference', { side: 'left' }, { wrongFirst: true });

    await select(side, 'right');
    await noOldReceipt();
    await collect('right-reference', { side: 'right' });

    await select(centre, 'D');
    await noOldReceipt();
    await select(load, 3);
    await collect('right-scaled-load', { side: 'right', centre: 'D', load: 3 });
    await select(side, 'left');
    await noOldReceipt();
    await collect('left-scaled-load', { side: 'left', centre: 'D', load: 3 });

    await select(load, -2);
    await noOldReceipt();
    await collect('left-reversed-load', { side: 'left', centre: 'D', load: -2 });
    await select(side, 'right');
    await noOldReceipt();
    await collect('right-reversed-load', { side: 'right', centre: 'D', load: -2 });

    await select(load, 0);
    await noOldReceipt();
    await collect('zero-load', { side: 'right', centre: 'D', load: 0 });
    await select(load, 1.5);
    await noOldReceipt();
    assert.match(await page.locator('#section-selection').innerText(), /integer load/i);
    assert.equal(await record.isEnabled(), false);

    await control('Local replay').click();
    const history = page.locator('#history');
    await history.waitFor({ state: 'visible' });
    const events = await history.locator('summary').allTextContents();
    const localPayloads = (await history.locator('pre').allTextContents()).map(text => JSON.parse(text));
    assert.equal(events.length, records.length * 2 + 1);
    assert.match(events[0], /first prediction/i);
    assert.match(events[1], /retry/i);
    assert.match(events[2], /reveal/i);
    assert.equal(localPayloads.length, events.length);
    for (const [i, payload] of localPayloads.entries()) {
        const result = records[Math.max(0, Math.floor((i - 1) / 2))];
        assert.equal(payload.cut, 3);
        assert.equal(payload.side, result.receipt.query.side);
        assert.equal(payload.centre, result.receipt.query.centre);
        assert.ok(Number.isFinite(payload.elapsedMs) && payload.elapsedMs > 0);
        if (/reveal/i.test(events[i])) assert.equal(payload.elapsedMs, result.receipt.elapsedMs);
    }
    await page.screenshot({ path: join(directory, 'local-replay.png'), fullPage: true });

    await control('Learning insights').click();
    const insights = page.locator('#insights-panel');
    await insights.getByRole('heading', { name: mode === 'pilot' ? /Instructor view/i : 'Records from this browser' }).waitFor();
    const heading = insights.getByRole('heading', { name: /Week 04|truss section/i });
    const instructorRows = await heading.locator('xpath=following-sibling::table[1]').locator('tbody tr').evaluateAll(rows =>
        rows.map(row => Array.from(row.cells, cell => cell.textContent.trim())));
    assert.equal(instructorRows.length, events.length);
    const courseId = mode === 'pilot' ? 'DEMO-001' : 'local-unassigned';
    assert.ok(instructorRows.every(row => row[0] === courseId));
    assert.deepEqual(instructorRows.slice(0, 3).map(row => [row[1], row[3]]),
        [['first_prediction', 'No'], ['retry', 'No'], ['reveal', 'Yes']]);
    assert.equal(networkPosts.length, mode === 'pilot' ? events.length : 0);
    assert.ok(networkPosts.every(path => path === '/api/attempts'));
    assert.deepEqual(errors, []);
    await page.screenshot({ path: join(directory, 'learning-insights.png'), fullPage: true });
    await writeFile(join(directory, 'section-truss-replay.json'),
        JSON.stringify({ mode, records, events, localPayloads, instructorRows, networkPosts, errors }, null, 2));
} catch (error) {
    await page.screenshot({ path: join(directory, 'failure.png'), fullPage: true });
    await writeFile(join(directory, 'failure.json'),
        JSON.stringify({ error: String(error.stack ?? error), records, networkPosts, errors }, null, 2));
    throw error;
} finally {
    await browser.close();
}
