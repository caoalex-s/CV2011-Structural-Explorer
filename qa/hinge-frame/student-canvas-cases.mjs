/** Exercise the visible student workflow in a fresh Playwright browser context. */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';

export async function runStudentCanvasCases({ page, base, output, target = 'published' }) {
    await mkdir(output, { recursive: true });
    await page.goto(base);
    const records = [];
    const errors = [];
    page.on('pageerror', error => errors.push(String(error)));
    const canvas = page.locator('#canvas');
    const selected = page.locator('#section-member');
    const tool = name => page.locator(`button[data-tool="${name}"]`).click();
    const object = kind => canvas.locator(`[data-object="${kind}"]`);
    const field = name => page.locator(`[data-property="${name}"]`);
    const closeProperties = page.getByRole('button', { name: 'Close properties' });
    const initialDocument = await page.request.get(base);
    const verification = await page.request.get(new URL('verification.json', base).href);
    const served = {
        url: page.url(), documentStatus: initialDocument.status(),
        documentSha256: createHash('sha256').update(await initialDocument.body()).digest('hex'),
        verificationStatus: verification.status(),
        verification: verification.ok() ? await verification.json().catch(() => null) : null,
    };

    async function blank() {
        await page.getByLabel('Start from').selectOption({ label: 'Blank canvas' });
        await page.getByRole('button', { name: 'Open example' }).click();
        assert.equal(await object('member').count(), 0);
        if (!(await page.getByLabel('Grid spacing (m)').isVisible())) {
            await page.getByText('Snapping', { exact: true }).click();
        }
        await page.getByLabel('Snap to grid and geometry').check();
        await page.getByLabel('Grid spacing (m)').fill('0.5');
        await page.getByLabel('Grid spacing (m)').press('Tab');
    }

    async function point(x, y = 0) {
        // The blank-canvas grid has a fixed view until Fit or Zoom is used.
        if (target === 'stage2' || target === 'stage3') {
            assert.equal(await closeProperties.isVisible(), false, 'Placement tool left the previous Properties panel open');
        } else if (await closeProperties.isVisible()) {
            await closeProperties.click();
        }
        await canvas.scrollIntoViewIfNeeded();
        const hit = await canvas.evaluate((svg, [x, y]) => {
            const viewPoint = new DOMPoint(500 + (x - 4) * 85, 200 - y * 85);
            const screen = viewPoint.matrixTransform(svg.getScreenCTM());
            const target = document.elementFromPoint(screen.x, screen.y);
            return { point: [screen.x, screen.y], onCanvas: svg.contains(target), target: target?.tagName };
        }, [x, y]);
        assert.ok(hit.onCanvas, `Canvas point (${x}, ${y}) hit ${hit.target} instead`);
        await page.mouse.click(...hit.point);
    }

    async function member(a, b) {
        await tool('member');
        await point(...a);
        await point(...b);
    }

    async function put(kind, x, y = 0) {
        await tool(kind);
        await point(x, y);
    }

    async function setNumber(name, value) {
        await field(name).fill(String(value));
        await field(name).press('Tab');
    }

    async function section(memberIndex, position) {
        await selected.selectOption({ index: memberIndex });
        const slider = page.locator('#section-position');
        // Use the standard slider keyboard controls at the exercised positions.
        await slider.press(position === 1 ? 'End' : 'Home');
        if (position === 0.5) for (let step = 0; step < 5; step++) await slider.press('PageUp');
        assert.equal(Number(await slider.inputValue()), position * 1000);
    }

    async function capture(name, expected) {
        const reactions = page.locator('.support-reactions');
        if (await reactions.isVisible() && !await reactions.evaluate(element => element.open)) {
            await reactions.locator('summary').click();
        }
        const entry = {
            name, expected,
            status: await page.locator('#status').innerText(),
            reactions: await reactions.isVisible() ? await page.locator('#reactions').innerText() : null,
            section: await page.locator('#section-distance').innerText(),
            response: await page.locator('#section-results').innerText(),
            checker: await page.locator('#portal-status').innerText(),
            checkerIntroduction: await page.locator('#portal-introduction').innerText(),
            workedSolution: await page.locator('#frame-worked-output').innerText(),
            supportCount: await object('support').count(),
        };
        records.push(entry);
        await page.screenshot({ path: join(output, `${name}.png`), fullPage: true });
        return entry;
    }

    async function worked() {
        await page.getByRole('button', { name: 'Generate worked solution' }).click();
        // First activation can reload the model. Observe a finished result or rejection.
        await page.locator('#portal-status')
            .filter({ hasText: /accepted|unsupported|inconclusive|error|failed|mechanism/i })
            .filter({ hasNotText: 'keep the original portal and change only its uniform BC load' })
            .waitFor({ state: 'visible', timeout: 40000 });
    }

    async function checkStage2(name, expected, checkerStatus) {
        if (target === 'published') return;
        try {
            await worked();
            const entry = await capture(name, expected);
            assert.match(entry.checker, checkerStatus);
            assert.ok(entry.workedSolution.trim(), 'Generate did not display the worked solution');
        } catch (error) {
            records.push({ name, failure: String(error), checker: await page.locator('#portal-status').innerText() });
        }
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

    function assertCanvasMemberName(entry, name) {
        assert.ok(entry.workedSolution.includes(`Member ${name}`), `Worked solution is missing member ${name}`);
        assert.doesNotMatch(entry.workedSolution, /\b(?:Node J|Member M)[0-9a-f]{6}\b/);
    }

    async function checkInclinedRelease(name, memberIndex, parameter, memberName, expected) {
        await selected.selectOption({ index: memberIndex });
        const parameterInput = page.locator('#frame-parameter');
        await parameterInput.fill(String(parameter));
        assert.equal(Number(await parameterInput.inputValue()), parameter);
        await worked();
        const entry = await capture(name, expected);
        assert.match(entry.status, /^Stable/);
        assert.match(entry.checker, /^Accepted/i);
        assert.equal(entry.supportCount, 2);
        assertCanvasMemberName(entry, memberName);

        // Compare the hand values with the interval endpoints shown to students.
        const solution = page.locator('#frame-worked-output');
        const tableAfter = label => solution.getByRole('heading', { name: label, exact: true })
            .locator('xpath=following-sibling::table[1]');
        async function compareIntervals(table, values) {
            const intervals = await table.locator('[data-evidence="outward-enclosure"]').allTextContents();
            assert.ok(intervals.length >= values.length, 'Missing checked intervals');
            for (const [i, reference] of values.entries()) {
                const bounds = /^\s*\[\s*(-?[\d.]+),\s*(-?[\d.]+)\s*\]\s*$/.exec(intervals[i]);
                assert.ok(bounds, `Invalid outward interval: ${intervals[i]}`);
                const [, lower, upper] = bounds.map(Number);
                const roundingSlack = 16 * Number.EPSILON * Math.max(1, Math.abs(reference));
                assert.ok(lower - roundingSlack <= reference && reference <= upper + roundingSlack,
                    `Hand value ${reference} is outside ${intervals[i]}`);
                assert.ok(upper - lower < 4e-6, `Unexpectedly wide force or moment interval: ${intervals[i]}`);
            }
        }
        await compareIntervals(tableAfter('Selected section'), expected.sectionNVM);
        await compareIntervals(tableAfter('Node A'), expected.reactionA);
        await compareIntervals(tableAfter('Node C'), expected.reactionC);
    }

    await scenario('simple-beam', async () => {
        await member([0, 0], [8, 0]);
        await put('pin', 0);
        await put('roller', 8);
        assert.equal(await field('angle').inputValue(), '90');
        assert.equal(await object('support').count(), 2);
        await put('force', 4);
        await setNumber('fy', -10);
        await capture('simple-beam-overview', 'Ay=By=5 kN, M at 4 m=20 kN m, stable determinate');
        await worked();
        await capture('simple-beam-worked', 'Accepted checked solution for the same beam');
    });

    await scenario('inclined-roller', async () => {
        await member([0, 0], [4, 2]);
        await put('pin', 0);
        await put('roller', 4, 2);
        await setNumber('angle', 45);
        await put('force', 4, 2);
        await setNumber('fy', -10);
        await capture('inclined-roller-overview', 'A=(-20,-10) kN and B=(20,20) kN by global equilibrium');
        await worked();
        const entry = await capture('inclined-roller-worked', 'Accepted checked intervals containing the hand reactions');
        if (target === 'stage3') {
            assert.match(entry.checker, /^Accepted/i);
            assertCanvasMemberName(entry, 'AB');
        }
    });

    await scenario('interior-hinge', async () => {
        await member([0, 0], [4, 0]);
        await member([4, 0], [8, 0]);
        await put('fixed', 0);
        await put('roller', 8);
        assert.equal(await field('angle').inputValue(), '90');
        assert.equal(await object('support').count(), 2);
        await put('force', 6);
        await setNumber('fy', -10);
        await put('joint', 4);
        await page.getByLabel('Joint connection').selectOption({ label: 'Internal pin / hinge' });
        assert.equal(await canvas.locator('[data-joint-symbol="pinned"]').count(), 1);
        await section(1, 0);
        await capture('hinge-at-right-span-start', 'Ay=Cy=5 kN, MA=20 kN m CCW, M(B+)=0');
        await section(1, 0.5);
        await capture('hinge-right-span-midpoint', 'M at the right-span midpoint=10 kN m');
        try {
            await worked();
            await capture('hinge-worked', target === 'published'
                ? 'Stage 1 should give a checked-scope rejection for a rotational release'
                : 'A Stage 2 candidate with a built checker should accept the stable hinge');
        } catch (error) {
            records.push({ name: 'hinge-worked', failure: String(error), checker: await page.locator('#portal-status').innerText() });
        }

        // Place the same couple on each physical side using Attached member.
        await put('moment', 4);
        await page.getByLabel('Attached member').selectOption({ index: 0 });
        await capture('hinge-left-couple', '20 kN m CCW on AB side: Ay=Cy=5 kN, MA=0');
        await checkStage2('hinge-left-couple-worked', 'The loaded AB face has M=+20 kN m and the BC face has M=0', /Accepted by the compiled hinge checker/);
        await page.getByLabel('Attached member').selectOption({ index: 1 });
        await capture('hinge-right-couple', '20 kN m CCW on BC side: Ay=10 kN, Cy=0, MA=40 kN m CCW');
        await checkStage2('hinge-right-couple-worked', 'The AB face has M=0 and the loaded BC face has M=-20 kN m', /Accepted by the compiled hinge checker/);
        await page.getByRole('button', { name: 'Delete selected object' }).click();
        await put('pin', 0);
        await capture('hinge-pin-mechanism', 'Replacing fixed A with a pin creates a mechanism');
        await checkStage2('hinge-pin-mechanism-worked', 'The downward load does work on the mechanism motion', /Checked mechanism.*incompatible/i);
        await put('fixed', 0);
        await put('roller', 8);
        await page.getByRole('button', { name: 'Delete selected object' }).click();
        await capture('hinge-no-roller-mechanism', 'Removing roller C leaves the right span free to rotate');
        await checkStage2('hinge-no-roller-mechanism-worked', 'The downward load does work on the mechanism motion', /Checked mechanism.*incompatible/i);
    });

    await scenario('released-branch', async () => {
        await member([0, 0], [4, 0]);
        await member([4, 0], [8, 0]);
        await member([4, 0], [4, 2]);
        await put('fixed', 0);
        await put('roller', 8);
        await put('pin', 4, 2);
        await put('joint', 4);
        const reference = page.getByLabel('Reference member');
        await reference.selectOption({ index: 0 });
        const rotations = page.locator('select[data-direction="rotation"]');
        assert.equal(await rotations.count(), 2);
        await rotations.last().selectOption({ label: 'Released' });
        assert.deepEqual(await rotations.evaluateAll(elements => elements.map(element => element.value)), ['rigid', 'free']);
        await capture('one-released-branch', 'Stable, AB/BC continuous and the vertical branch released in rotation');
        await put('force', 4, 1);
        await setNumber('fx', 10);
        await setNumber('fy', 0);
        await capture('loaded-released-branch', 'The 10 kN horizontal load gives a -5 kN horizontal reaction at D and zero branch-end moment at B');
        await checkStage2('loaded-released-branch-worked', 'The released branch face at B has zero end moment', /Accepted by the compiled hinge checker/);
        await put('joint', 0);
        assert.equal(await rotations.count(), 0);
        await capture('single-member-end-editor', 'Single incident member offers no side-specific release control');
    });

    if (target === 'stage3') for (const reversed of [false, true]) {
        const direction = reversed ? 'reversed' : 'forward';
        const inclinedName = reversed ? 'CB' : 'BC';
        const hingeParameter = reversed ? 1 : 0;
        const quarterParameter = reversed ? 0.75 : 0.25;
        const orientation = reversed ? -1 : 1;

        await scenario(`inclined-release-${direction}`, async () => {
            await member([0, 0], [4, 0]);
            await member(reversed ? [8, 2] : [4, 0], reversed ? [4, 0] : [8, 2]);
            await put('fixed', 0);
            await put('roller', 8, 2);
            await setNumber('angle', 45);
            assert.equal(await object('support').count(), 2);
            await put('force', 6, 1);
            await setNumber('t', 0.5); // Numeric edit removes distance-grid rounding on the incline.
            await setNumber('fy', -10);
            await put('joint', 4);
            await page.getByLabel('Joint connection').selectOption({ label: 'Internal pin / hinge' });
            assert.equal(await canvas.locator('[data-joint-symbol="pinned"]').count(), 1);

            // Moments on the B–C free body about B give 2 Cx = 20 - Q_BC,
            // because Cx = Cy. Moments about A then give MA = 60 - 6 Cx - Q.
            // On the B face the retained-end force is (-Cx, 10 - Cy). In
            // B-to-C axes (c,s)=(2,1)/sqrt(5), N=-c Bx-s By and V=-s Bx+c By.
            // At 1/4 of the physical span from B, M=-Q_BC+V*sqrt(5)/2.
            const baseline = { sectionNVM: [20 / Math.sqrt(5), 10 / Math.sqrt(5), 5 * orientation],
                reactionA: [-10, 0, 0], reactionC: [10, 10, 0] };
            await checkInclinedRelease(`${direction}-quarter`, 1, quarterParameter, inclinedName, baseline);

            await put('moment', 4);
            const attachment = page.getByLabel('Attached member');
            await attachment.selectOption({ index: 0 });
            await setNumber('t', 1);
            await setNumber('mz', 10);
            const onAB = { reactionA: [-10, 0, -10], reactionC: [10, 10, 0] };
            await checkInclinedRelease(`${direction}-couple-ab-loaded-face`, 0, 1, 'AB',
                { ...onAB, sectionNVM: [10, 0, 10] });
            await checkInclinedRelease(`${direction}-couple-ab-released-face`, 1, hingeParameter, inclinedName,
                { ...onAB, sectionNVM: [baseline.sectionNVM[0], baseline.sectionNVM[1], 0] });

            await attachment.selectOption({ index: 1 });
            await setNumber('t', hingeParameter);
            const onIncline = { reactionA: [-5, 5, 20], reactionC: [5, 5, 0] };
            const inclinedAxial = Math.sqrt(5);
            const inclinedShear = 15 / Math.sqrt(5);
            await checkInclinedRelease(`${direction}-couple-incline-unloaded-face`, 0, 1, 'AB',
                { ...onIncline, sectionNVM: [5, 5, 0] });
            await checkInclinedRelease(`${direction}-couple-incline-loaded-face`, 1, hingeParameter, inclinedName,
                { ...onIncline, sectionNVM: [inclinedAxial, inclinedShear, -10 * orientation] });
            await checkInclinedRelease(`${direction}-couple-incline-quarter`, 1, quarterParameter, inclinedName,
                { ...onIncline, sectionNVM: [inclinedAxial, inclinedShear, -2.5 * orientation] });
            if (!reversed) {
                await put('moment', 4);
                await attachment.selectOption({ index: 1 });
                await setNumber('t', 0);
                await setNumber('mz', -4);
                await checkInclinedRelease('two-couples-on-inclined-end', 1, 0, inclinedName,
                    { reactionA: [-7, 3, 12], reactionC: [7, 7, 0], sectionNVM: [11/Math.sqrt(5), 13/Math.sqrt(5), -6] });
                const output = await page.locator('#frame-worked-output').innerText();
                assert.ok(output.includes('10 kN m, -4 kN m'), 'Individual applied couples missing from the worked solution');
            }
        });
    }

    await writeFile(join(output, `student-canvas-${target}.json`), JSON.stringify({ target, served, records, errors }, null, 2) + '\n');
    return { served, records, errors };
}
