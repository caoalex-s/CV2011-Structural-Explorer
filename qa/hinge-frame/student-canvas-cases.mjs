/** Exercise the visible student workflow in a fresh Playwright browser context. */
import assert from 'node:assert/strict';
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
        await canvas.scrollIntoViewIfNeeded();
        const screenPoint = await canvas.evaluate((svg, [x, y]) => {
            const viewPoint = new DOMPoint(500 + (x - 4) * 85, 200 - y * 85);
            const screen = viewPoint.matrixTransform(svg.getScreenCTM());
            return [screen.x, screen.y];
        }, [x, y]);
        await page.mouse.click(...screenPoint);
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
        };
        records.push(entry);
        await page.screenshot({ path: join(output, `${name}.png`), fullPage: true });
        return entry;
    }

    async function worked() {
        await page.getByRole('button', { name: 'Generate worked solution' }).click();
        // First activation can reload the model. Observe a finished result or rejection.
        await page.locator('#portal-status').filter({ hasText: /accepted|unsupported|inconclusive|error|failed|mechanism/i })
            .waitFor({ state: 'visible', timeout: 40000 });
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

    await scenario('simple-beam', async () => {
        await member([0, 0], [8, 0]);
        await put('pin', 0);
        await put('roller', 8);
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
        await capture('inclined-roller-worked', 'Accepted checked intervals containing the hand reactions');
    });

    await scenario('interior-hinge', async () => {
        await member([0, 0], [4, 0]);
        await member([4, 0], [8, 0]);
        await put('fixed', 0);
        await put('roller', 8);
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
        await page.getByLabel('Attached member').selectOption({ index: 1 });
        await capture('hinge-right-couple', '20 kN m CCW on BC side: Ay=10 kN, Cy=0, MA=40 kN m CCW');
        await page.getByRole('button', { name: 'Delete selected object' }).click();
        await put('pin', 0);
        await capture('hinge-pin-mechanism', 'Replacing fixed A with a pin creates a mechanism');
        await put('fixed', 0);
        await put('roller', 8);
        await page.getByRole('button', { name: 'Delete selected object' }).click();
        await capture('hinge-no-roller-mechanism', 'Removing roller C leaves the right span free to rotate');
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
        await put('joint', 0);
        assert.equal(await rotations.count(), 0);
        await capture('single-member-end-editor', 'Single incident member offers no side-specific release control');
    });

    await writeFile(join(output, `student-canvas-${target}.json`), JSON.stringify({ target, records, errors }, null, 2) + '\n');
    return { records, errors };
}
