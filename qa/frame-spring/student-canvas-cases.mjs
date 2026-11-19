/** Independent hand checks using a fresh Playwright page and visible drawing tools.
 * Optional validateWorked receives the captured worked text and the hand values
 * so the runner can also check the final spring-specific readout format.
 */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';

const length = 4; // Each horizontal half, in m.
const bendingRigidity = 20000; // kN m², the draw tool's default.
const rotationStiffness = 5000; // kN m/rad.

/** Pure tip couple gives zero N and V. Integrate M/EI over each member
 * and add the angle jump at B. Rotation is CCW in both member directions.
 */
export function tipCoupleReference(stiffness, inclinedLength = length, reversed = false) {
    const couple = 20;
    const referenceRotation = couple * length / bendingRigidity;
    const rotationJump = Number.isFinite(stiffness) ? couple / stiffness : 0;
    return {
        stiffness: Number.isFinite(stiffness) ? stiffness : 'continuous',
        rotationJump, referenceRotation, springMoment: couple,
        section: [0, 0, reversed ? -couple : couple,
            referenceRotation + rotationJump + couple * inclinedLength / bendingRigidity],
        reactions: [[0, 0, -couple]],
    };
}

/** Symmetry gives vertical force P/2 on each half. For the left half,
 * theta_B = -P L²/(4 EI) + M_B L/EI and M_B = k (-2 theta_B).
 * A rigid joint sets theta_B = 0. A zero-stiffness hinge has M_B = 0.
 */
export function redistributionReference(stiffness) {
    const load = 10;
    const springMoment = Number.isFinite(stiffness)
        ? stiffness * load * length ** 2 / (2 * (bendingRigidity + 2 * stiffness * length))
        : load * length / 4;
    const referenceRotation = -load * length ** 2 / (4 * bendingRigidity) + springMoment * length / bendingRigidity;
    const supportMoment = load * length / 2 - springMoment;
    return {
        stiffness: Number.isFinite(stiffness) ? stiffness : 'continuous',
        rotationJump: -2 * referenceRotation, referenceRotation, springMoment,
        section: [0, 5, springMoment, referenceRotation],
        reactions: [[0, 5, supportMoment], [0, 5, -supportMoment]],
    };
}

export async function runSpringStudentCases({ page, base, output, validateWorked }) {
    await mkdir(output, { recursive: true });
    const records = [];
    const errors = [];
    page.on('pageerror', error => errors.push(String(error)));
    await page.goto(base);
    const canvas = page.locator('#canvas');
    const inspector = page.locator('#inspector');
    const field = key => inspector.locator(`[data-property="${key}"]`);
    const chooseTool = name => page.locator(`button[data-tool="${name}"]`).click();

    // 1. Draw and edit the model through the same controls students use.
    async function blank() {
        await page.getByLabel('Start from').selectOption({ label: 'Blank canvas' });
        await page.getByRole('button', { name: 'Open example' }).click();
        assert.equal(await canvas.locator('[data-object="member"]').count(), 0);
        const grid = page.getByLabel('Grid spacing (m)');
        if (!(await grid.isVisible())) await page.getByText('Snapping', { exact: true }).click();
        await page.getByLabel('Snap to grid and geometry').check();
        await grid.fill('0.5');
        await grid.press('Tab');
    }

    async function point(x, y = 0) {
        assert.equal(await page.getByRole('button', { name: 'Close properties' }).isVisible(), false,
            'Placement tool left the preceding Properties panel open');
        await canvas.scrollIntoViewIfNeeded();
        const hit = await canvas.evaluate((svg, [x, y]) => {
            // Blank canvas resets its view to x=4, y=0 at 85 SVG units per metre.
            const p = new DOMPoint(500 + (x - 4) * 85, 200 - y * 85).matrixTransform(svg.getScreenCTM());
            return { x: p.x, y: p.y, canvas: svg.contains(document.elementFromPoint(p.x, p.y)) };
        }, [x, y]);
        assert.ok(hit.canvas, `Drawing point (${x}, ${y}) is obstructed`);
        await page.mouse.click(hit.x, hit.y);
    }

    async function member(a, b) {
        await chooseTool('member');
        await point(...a);
        await point(...b);
    }

    async function place(tool, x, y = 0) {
        await chooseTool(tool);
        await point(x, y);
    }

    async function numberField(locator, value) {
        await locator.fill(String(value));
        await locator.press('Tab');
    }

    async function spring(stiffness, explicit = false) {
        await place('joint', 4);
        if (explicit) {
            const rotation = inspector.locator('select[data-direction="rotation"]');
            assert.equal(await rotation.count(), 1);
            await rotation.selectOption({ label: 'Elastic spring' });
            await numberField(inspector.locator('input[data-direction="rotation"][data-stiffness]'), stiffness);
        } else {
            await page.getByLabel('Joint connection').selectOption({ label: 'Semi-rigid joint' });
            await numberField(field('rotationStiffness'), stiffness);
        }
    }

    async function selectSection(memberIndex, atEnd) {
        await page.locator('#section-member').selectOption({ index: memberIndex });
        const slider = page.getByRole('slider', { name: 'Section position' });
        await slider.press(atEnd ? 'End' : 'Home');
        assert.equal(Number(await slider.inputValue()), atEnd ? 1000 : 0);
    }

    // 2. Compare the ordinary UI readouts before asking for a checked solution.
    function closeTo(observed, expected, label, digits = 3) {
        // Allow one half-unit in the last significant digit shown by the UI.
        const tolerance = expected === 0 ? 1e-7 : 0.501 * 10 ** (Math.floor(Math.log10(Math.abs(expected))) + 1 - digits);
        assert.ok(Number.isFinite(observed) && Math.abs(observed - expected) <= tolerance,
            `${label}: expected ${expected}, observed ${observed}`);
    }

    async function check(name, memberIndex, atEnd, expected) {
        await selectSection(memberIndex, atEnd);
        const status = await page.locator('#status').innerText();
        const response = await page.locator('#section-results strong').allTextContents();
        const reactions = page.locator('.support-reactions');
        if (await reactions.isVisible() && !await reactions.evaluate(details => details.open)) {
            await reactions.locator('summary').click();
        }
        const rows = await page.locator('#reactions .reaction-row').allTextContents();
        const properties = await inspector.innerText();
        const entry = { name, expected, status, response, rows, properties };
        records.push(entry);
        assert.match(status, /^Stable/);
        expected.section.forEach((value, index) => {
            // The fourth overview field is rotation in mrad, while the hand value is in rad.
            closeTo(Number.parseFloat(response[index]), index === 3 ? value * 1000 : value, `${name} section ${index}`, 4);
        });
        assert.equal(rows.length, expected.reactions.length);
        for (const [i, row] of rows.entries()) {
            // KaTeX labels contain duplicate accessible math text; only text
            // after the explicit separator colon represents a displayed value.
            const values = [...row.matchAll(/:\s*(-?[\d.]+(?:e[+-]?\d+)?)/gi)].map(match => Number(match[1]));
            assert.ok(values.length === 2 || values.length === 3, `Could not read reaction row: ${row}`);
            expected.reactions[i].forEach((value, j) => closeTo(values[j] ?? 0, value, `${name} reaction ${i}/${j}`));
        }
        const shownJump = /Relative rotation Δθ =\s*(-?[\d.]+(?:e[+-]?\d+)?)/i.exec(properties);
        if (expected.stiffness !== 'continuous') {
            assert.ok(shownJump, 'The joint inspector did not display relative rotation');
            closeTo(Number(shownJump[1]), expected.rotationJump, `${name} relative rotation`);
        }
        await page.getByRole('button', { name: 'Generate worked solution' }).click();
        const checker = page.locator('#portal-status');
        await checker.filter({ hasText: /^(Accepted|Checked mechanism|Check |Error|Unsupported|Checking unavailable)/i })
            .waitFor({ state: 'visible', timeout: 40000 });
        entry.checker = await checker.innerText();
        entry.workedSolution = await page.locator('#frame-worked-output').innerText();
        assert.match(entry.checker, /^Accepted/i);
        assert.ok(entry.workedSolution.trim(), 'Generate did not render a worked solution');
        if (typeof expected.stiffness === 'number' && expected.stiffness > 0) {
            const receipt = JSON.parse(await page.locator('#portal-certificate').textContent());
            const hash = bytes => createHash('sha256').update(bytes).digest('hex');
            assert.equal(receipt.protocol, 'CV2011_ROTATIONAL_SPRING_1');
            assert.match(receipt.artifact, /^[0-9a-f]{64}$/);
            assert.match(receipt.bundle, /^[0-9a-f]{64}$/);
            assert.equal(hash(JSON.stringify(receipt.sourceRequest)), receipt.inputDigest);
            assert.equal(hash(receipt.packet), receipt.packetDigest);
            assert.equal(hash(receipt.report), receipt.reportDigest);
            assert.equal(receipt.sourceRequest.query.member, await page.locator('#section-member').inputValue());
            assert.equal(receipt.sourceRequest.query.parameter, atEnd ? 1 : 0);
            entry.receipt = { artifact: receipt.artifact, bundle: receipt.bundle, inputDigest: receipt.inputDigest,
                packetDigest: receipt.packetDigest, reportDigest: receipt.reportDigest };
            const springSide = page.locator('#frame-worked-output [data-spring-side]');
            assert.equal(await springSide.count(), 1);
            const values = { 'relative-rotation': expected.rotationJump, 'transmitted-moment': expected.springMoment,
                'reference-rotation': expected.referenceRotation, 'end-rotation': expected.referenceRotation + expected.rotationJump };
            entry.springIntervals = {};
            const rationalNumber = text => {
                assert.match(text ?? '', /^-?\d+(?:\/\d+)?$/);
                const [numerator, denominator = '1'] = text.split('/');
                return Number(numerator) / Number(denominator);
            };
            for (const [quantity, reference] of Object.entries(values)) {
                const readout = springSide.locator(`[data-spring-value="${quantity}"]`);
                assert.ok(await readout.isVisible(), `Missing visible checked ${quantity}`);
                const lower = await readout.getAttribute('data-lower');
                const upper = await readout.getAttribute('data-upper');
                const lo = rationalNumber(lower), hi = rationalNumber(upper);
                const slack = 8 * Number.EPSILON * Math.max(1, Math.abs(reference));
                assert.ok(lo <= hi && lo - slack <= reference && reference <= hi + slack,
                    `${quantity}: ${reference} outside [${lower}, ${upper}]`);
                entry.springIntervals[quantity] = { lower, upper };
            }
        }
        if (validateWorked) await validateWorked({ page, entry });
        await page.screenshot({ path: join(output, `${name}.png`), fullPage: true });
    }

    async function scenario(name, run) {
        try {
            await blank();
            await run();
        } catch (error) {
            records.push({ name, failure: String(error.stack ?? error) });
            await page.screenshot({ path: join(output, `${name}-failure.png`), fullPage: true });
        }
    }

    // 3. Exercise stiffness changes, both limit models, and member orientation.
    await scenario('spring-tip-couple', async () => {
        await member([0, 0], [4, 0]);
        await member([4, 0], [8, 0]);
        await place('fixed', 0);
        await place('moment', 8);
        await numberField(field('t'), 1);
        await numberField(field('mz'), 20);
        await spring(rotationStiffness);
        await check('spring-tip-couple', 1, true, tipCoupleReference(rotationStiffness));
        await spring(2 * rotationStiffness);
        await check('spring-tip-couple-double-k', 1, true, tipCoupleReference(2 * rotationStiffness));
        await place('joint', 4);
        await numberField(field('rotationStiffness'), 0);
        assert.equal(await page.getByLabel('Joint connection').inputValue(), 'pinned');
        assert.equal(await inspector.locator('select[data-direction="rotation"]').inputValue(), 'free');
        const status = await page.locator('#status').innerText();
        assert.match(status, /^Unstable \(mechanism\)/);
        await page.getByRole('button', { name: 'Generate worked solution' }).click();
        const checker = page.locator('#portal-status').filter({ hasText: /^Checked mechanism.*incompatible/i });
        await checker.waitFor({ state: 'visible', timeout: 40000 });
        const workedSolution = await page.locator('#frame-worked-output').innerText();
        assert.match(workedSolution, /nonzero mechanism motion/i);
        assert.equal(await page.locator('#frame-worked-output [data-spring-side]').count(), 0);
        records.push({ name: 'spring-tip-couple-zero-mechanism', status, checker: await checker.innerText(), workedSolution });
        await page.screenshot({ path: join(output, 'spring-tip-couple-zero-mechanism.png'), fullPage: true });
    });

    await scenario('spring-fixed-fixed', async () => {
        await member([0, 0], [4, 0]);
        await member([4, 0], [8, 0]);
        await place('fixed', 0);
        await place('fixed', 8);
        await place('force', 4);
        await numberField(field('fy'), -10);
        await spring(2500);
        await check('spring-fixed-fixed-k2500', 0, true, redistributionReference(2500));
        await spring(5000);
        await check('spring-fixed-fixed-k5000', 0, true, redistributionReference(5000));
        // Exercise the explicit end input as well as the preset input above.
        await spring(5000, true);
        await numberField(inspector.locator('input[data-direction="rotation"][data-stiffness]'), 0);
        assert.equal(await inspector.locator('select[data-direction="rotation"]').inputValue(), 'free');
        await check('spring-fixed-fixed-zero-limit', 0, true, redistributionReference(0));
        await place('joint', 4);
        await page.getByLabel('Joint connection').selectOption({ label: 'Rigid joint' });
        await check('spring-fixed-fixed-continuous-limit', 0, true, redistributionReference(Infinity));
    });

    for (const reversed of [false, true]) {
        const name = reversed ? 'spring-incline-reversed' : 'spring-incline-forward';
        await scenario(name, async () => {
            await member([0, 0], [4, 0]);
            await member(reversed ? [8, 2] : [4, 0], reversed ? [4, 0] : [8, 2]);
            await place('fixed', 0);
            await place('moment', 8, 2);
            await numberField(field('t'), reversed ? 0 : 1);
            await numberField(field('mz'), 20);
            await spring(rotationStiffness, true);
            await check(name, 1, !reversed, tipCoupleReference(rotationStiffness, Math.sqrt(20), reversed));
        });
    }

    // 4. Measure the labels and arcs at the same physical attachment, then
    // check that opening the second label selects its own signed action.
    async function checkCoupleLabels(name, jointHeight) {
        await member([0, 0], [4, 0]);
        if (jointHeight) {
            // Move the existing joint numerically while retaining its incidence.
            await place('joint', 4);
            await numberField(field('y'), jointHeight);
        }
        await member([4, jointHeight], [8, 0]);
        await place('fixed', 0);
        for (const magnitude of [10, -4]) {
            await place('moment', 4, jointHeight);
            await field('member').selectOption({ index: 1 });
            await numberField(field('t'), 0);
            await numberField(field('mz'), magnitude);
        }
        await page.getByRole('button', { name: 'Close properties' }).click();
        await page.evaluate(async () => { await document.fonts.ready; });
        const couples = canvas.locator('[data-object="load"] [data-vector="moment"]');
        const geometry = await couples.evaluateAll(vectors => vectors.map(vector => {
            const center = [Number(vector.dataset.originX), Number(vector.dataset.originY)];
            const arc = vector.querySelector('path.hit');
            const arcLength = arc.getTotalLength();
            const samples = [0, 0.25, 0.5, 0.75, 1].map(t => {
                const p = arc.getPointAtLength(t * arcLength);
                return [p.x, p.y];
            });
            const label = vector.querySelector('text');
            const { x, y, width, height } = label.getBoundingClientRect();
            return { center, samples, label: label.textContent, box: { x, y, width, height } };
        }));
        const canvasBox = await canvas.boundingBox();
        records.push({ name, geometry, canvasBox });
        assert.equal(geometry.length, 2);
        assert.deepEqual(geometry[0].center, [500, 200 - 85 * jointHeight]);
        assert.deepEqual(geometry[1].center, geometry[0].center);
        for (const { center, samples } of geometry) {
            const radii = samples.map(([x, y]) => Math.hypot(x - center[0], y - center[1]));
            assert.ok(Math.max(...radii) - Math.min(...radii) < 0.1, 'A couple arc moved away from its attachment');
        }
        const [a, b] = geometry.map(couple => couple.box);
        assert.ok(a.width > 0 && b.width > 0 && a.height > 0 && b.height > 0);
        assert.ok(canvasBox);
        for (const label of [a, b]) {
            assert.ok(label.x >= canvasBox.x && label.y >= canvasBox.y &&
                label.x + label.width <= canvasBox.x + canvasBox.width &&
                label.y + label.height <= canvasBox.y + canvasBox.height, 'A couple label is clipped by the canvas');
        }
        assert.ok(a.y + a.height <= b.y || b.y + b.height <= a.y || a.x + a.width <= b.x || b.x + b.width <= a.x,
            'The two couple label boxes overlap');
        await chooseTool('select');
        await couples.nth(1).locator('text').click();
        assert.equal(Number(await field('mz').inputValue()), -4);
        assert.equal(Number(await field('t').inputValue()), 0);
        assert.equal(await field('member').locator('option:checked').textContent(), 'B–C');
        await page.screenshot({ path: join(output, `${name}.png`), fullPage: true });
    }
    for (const [name, height] of [['coincident-couples', 0], ['coincident-couples-near-top', 2]]) {
        await scenario(name, () => checkCoupleLabels(name, height));
    }

    const result = { records, errors };
    await writeFile(join(output, 'student-canvas-springs.json'), JSON.stringify(result, null, 2) + '\n');
    return result;
}
