/** Hand references and MAIN worked-solution checks for exact cardinal frames.
 * Run with a fresh Playwright page and the synthetic development site URL.
 */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';

// On the antisymmetrically loaded portal, B and C have opposite vertical
// translations and a common horizontal displacement and CCW rotation.
// Eliminating horizontal sway leaves the 2×2 system for (v_B, theta_B).
const portal = { height: 4, length: 6, EA: 2000000, EI: 20000, w0: 6 };
const portalShear = 3510 / 563;
const portalStartMoment = -396 / 563;

function piece(start, end, shear, moment) {
    return { start, end, shear, moment };
}

function candidate(field, side, index, x, value, minimum = false, maximum = false) {
    return { field, side, index, x, value, minimum, maximum };
}

function affineReference(startShear, startMoment, discriminant) {
    // w = 6−2x kN/m, so V' = −w and M' = V. The zero of w is
    // the shear minimum. The two zeros of V locate the moment extrema.
    const [numerator, denominator] = discriminant;
    const offset = Math.sqrt(numerator / denominator);
    const momentMagnitude = 2 * offset ** 3 / 3;
    const maximum = candidate('M', 'interior', 0, 3 - offset, momentMagnitude, false, true);
    const minimum = candidate('M', 'interior', 0, 3 + offset, -momentMagnitude, true);
    maximum.radicals = { x: [3, -1, 1, numerator, denominator],
        y: [0, 2 * numerator, 3 * denominator, numerator, denominator] };
    minimum.radicals = { x: [3, 1, 1, numerator, denominator],
        y: [0, -2 * numerator, 3 * denominator, numerator, denominator] };
    return {
        pieces: [piece(0, 6, [startShear, -6, 1], [startMoment, startShear, -3, 1 / 3])],
        candidates: [
            candidate('V', 'start', 0, 0, startShear, false, true),
            candidate('V', 'end', 0, 6, startShear, false, true),
            candidate('V', 'interior', 0, 3, startShear - 9, true),
            candidate('M', 'start', 0, 0, startMoment),
            candidate('M', 'end', 0, 6, -startMoment),
            maximum, minimum,
        ],
    };
}

export const handReferences = {
    portal: affineReference(portalShear, portalStartMoment, [1557, 563]),
    pinRoller: affineReference(6, 0, [3, 1]),
    jumps: {
        // L=8, downward 12 kN at x=2 and +6 kN m at x=4.
        // Moment balance gives B_y=(12*2−6)/8=2.25 and A_y=9.75.
        pieces: [piece(0, 2, [9.75], [0, 9.75]), piece(2, 4, [-2.25], [19.5, -2.25]),
            piece(4, 8, [-2.25], [9, -2.25])],
        candidates: [
            candidate('V', 'flat', 0, [0, 2], 9.75, false, true),
            candidate('V', 'flat', 1, [2, 4], -2.25, true),
            candidate('V', 'flat', 2, [4, 8], -2.25, true),
            candidate('V', 'end', 0, 2, 9.75, false, true),
            candidate('V', 'start', 1, 2, -2.25, true),
            candidate('M', 'start', 0, 0, 0, true),
            candidate('M', 'end', 0, 2, 19.5, false, true),
            candidate('M', 'start', 1, 2, 19.5, false, true),
            candidate('M', 'end', 1, 4, 15),
            candidate('M', 'start', 2, 4, 9),
            candidate('M', 'end', 2, 8, 0, true),
        ],
    },
    unloaded: {
        pieces: [piece(0, 6, [0], [0])],
        candidates: ['V', 'M'].map(field => candidate(field, 'flat', 0, [0, 6], 0, true, true)),
    },
};

function readRational(text) {
    assert.match(text ?? '', /^-?\d+\/\d+$/);
    const [top, bottom] = text.split('/').map(Number);
    assert.ok(Number.isFinite(top) && Number.isFinite(bottom) && bottom > 0);
    return top / bottom;
}

function compare(observed, expected) {
    assert.ok(Math.abs(observed - expected) <= 24 * Number.EPSILON * Math.max(1, Math.abs(expected)),
        `Expected ${expected}, received ${observed}`);
}

function contains(lower, upper, expected) {
    const slack = 24 * Number.EPSILON * Math.max(1, Math.abs(expected));
    return lower <= upper && lower - slack <= expected && expected <= upper + slack;
}

/** Compare a report endpoint q with a + (b/c) sqrt(d/e) exactly.
 * First compare signs of q-a and b. Square only when signs agree.
 */
export function compareRationalToRadical(endpoint, radical) {
    const [top, bottom] = endpoint.split('/').map(BigInt);
    const [a, b, c, d, e] = radical.map(BigInt);
    const shifted = top - a * bottom;
    const sign = value => value < 0n ? -1 : value > 0n ? 1 : 0;
    const leftSign = sign(shifted), rightSign = d === 0n ? 0 : sign(b);
    if (leftSign !== rightSign) return leftSign < rightSign ? -1 : 1;
    if (leftSign === 0) return 0;
    const comparison = shifted ** 2n * c ** 2n * e - b ** 2n * bottom ** 2n * d;
    return leftSign * sign(comparison);
}

export function compareDiagram(observed, expected) {
    assert.equal(observed.pieces.length, expected.pieces.length);
    for (const [index, reference] of expected.pieces.entries()) {
        const readout = observed.pieces[index];
        compare(readRational(readout.start), reference.start);
        compare(readRational(readout.end), reference.end);
        for (const field of ['shear', 'moment']) {
            const coefficients = readout[field].split(',').map(value => readRational(value.trim()));
            assert.ok(coefficients.length >= reference[field].length);
            coefficients.forEach((coefficient, power) => compare(coefficient, reference[field][power] ?? 0));
        }
    }
    for (const ref of expected.candidates) {
        const options = observed.candidates.filter(row => row.field === ref.field && row.side === ref.side &&
            Number(row.pieceIndex) === ref.index);
        const matching = options.filter(row => {
            const lower = readRational(row.xLow), upper = readRational(row.xHigh);
            return Array.isArray(ref.x) ? Math.abs(lower - ref.x[0]) <= 1e-12 && Math.abs(upper - ref.x[1]) <= 1e-12
                : contains(lower, upper, ref.x) && upper - lower <= 1e-5;
        });
        assert.equal(matching.length, 1, `Missing or repeated ${ref.field} candidate at ${ref.x}, ${ref.side}`);
        const row = matching[0];
        const lower = readRational(row.yLow), upper = readRational(row.yHigh);
        assert.ok(contains(lower, upper, ref.value) && upper - lower <= 1e-5,
            `${ref.field} value ${ref.value} outside a narrow bound at ${ref.x}`);
        assert.equal(row.min, String(ref.minimum), `${ref.field} minimum flag at ${ref.x}`);
        assert.equal(row.max, String(ref.maximum), `${ref.field} maximum flag at ${ref.x}`);
        if (ref.radicals) for (const [axis, radical] of Object.entries(ref.radicals)) {
            assert.ok(compareRationalToRadical(row[axis + 'Low'], radical) < 0 &&
                compareRationalToRadical(row[axis + 'High'], radical) > 0,
            `Exact rational enclosure misses the irrational ${axis} at ${ref.x}`);
        }
    }
}

export async function runMemberDiagramStudentCases({ page, base, output }) {
    await mkdir(output, { recursive: true });
    const records = [], errors = [];
    page.on('pageerror', error => errors.push(String(error)));
    await page.goto(base);
    const canvas = page.locator('#canvas');
    const properties = page.locator('#inspector');
    const diagram = page.locator('#checked-member-diagram');
    const chooseTool = name => page.locator(`button[data-tool="${name}"]`).click();
    const closeProperties = page.getByRole('button', { name: 'Close properties' });
    let canvasScale = 85;

    async function blank() {
        await page.getByLabel('Start from').selectOption({ label: 'Blank canvas' });
        await page.getByRole('button', { name: 'Open example' }).click();
        canvasScale = 85;
        assert.equal(await canvas.locator('[data-object="member"]').count(), 0);
        const spacing = page.getByLabel('Grid spacing (m)');
        if (!(await spacing.isVisible())) await page.getByText('Snapping', { exact: true }).click();
        await page.getByLabel('Snap to grid and geometry').check();
        await spacing.fill('0.5');
        await spacing.press('Tab');
    }

    async function point(x, y = 0) {
        assert.equal(await closeProperties.isVisible(), false, 'Properties obscures a placement');
        await canvas.scrollIntoViewIfNeeded();
        const target = await canvas.evaluate((svg, [x, y, scale]) => {
            const p = new DOMPoint(500 + (x - 4) * scale, 200 - y * scale).matrixTransform(svg.getScreenCTM());
            return { x: p.x, y: p.y, onCanvas: svg.contains(document.elementFromPoint(p.x, p.y)) };
        }, [x, y, canvasScale]);
        assert.ok(target.onCanvas, `Drawing point (${x}, ${y}) did not hit canvas`);
        await page.mouse.click(target.x, target.y);
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

    async function setNumber(property, value) {
        const input = properties.locator(`[data-property="${property}"]`);
        await input.fill(String(value));
        await input.press('Tab');
    }

    async function selectDistributed() {
        if (await closeProperties.isVisible()) await closeProperties.click();
        await chooseTool('select');
        await canvas.locator('[data-object="load"]').locator('text').click();
        await properties.getByRole('heading', { name: 'Load properties' }).waitFor();
    }

    async function affineLoad(y) {
        // Start inside the beam to avoid attaching to an incident column at
        // the joint. Enter the exact full-span boundaries in the inspector.
        await chooseTool('distributed');
        await point(1, y);
        await point(5, y);
        await selectDistributed();
        await setNumber('t', 0);
        await setNumber('end', 1);
        await setNumber('fy', 6); // Downward-positive inspector value.
        await setNumber('qEnd', -6);
    }

    async function pinRoller(length) {
        await member([0, 0], [length, 0]);
        await place('pin', 0);
        await place('roller', length);
    }

    async function generate(name, expected, label) {
        await page.getByRole('button', { name: 'Generate worked solution' }).click();
        await diagram.waitFor({ state: 'visible', timeout: 40000 });
        const observed = {
            pieces: await diagram.locator('[data-piece]').evaluateAll(rows => rows.map(row => ({ ...row.dataset }))),
            candidates: await diagram.locator('[data-candidate]').evaluateAll(rows => rows.map(row => ({ ...row.dataset }))),
        };
        const status = await page.locator('#portal-status').innerText();
        const text = await diagram.innerText();
        const result = { name, expected, observed, status, text };
        records.push(result);
        assert.match(status, /^Accepted/i);
        assert.ok(text.includes(label), `Worked diagram must identify canvas member ${label}`);
        assert.match(text, /kN/);
        assert.match(text, /kN\s*[·⋅]?\s*m/);
        compareDiagram(observed, expected);
        const receipt = JSON.parse(await page.locator('#portal-certificate').textContent());
        const hash = contents => createHash('sha256').update(contents).digest('hex');
        assert.equal(receipt.diagram.protocol, 'CV2011_DIAGRAM_1');
        assert.equal(receipt.sourceRequest.query.member, await page.getByLabel('Inspect member').inputValue());
        assert.equal(hash(JSON.stringify(receipt.sourceRequest)), receipt.inputDigest);
        assert.equal(hash(receipt.packet), receipt.diagram.packetDigest);
        assert.equal(hash(receipt.diagram.report), receipt.diagram.reportDigest);
        const { artifact, bundle, packetDigest, reportDigest } = receipt.diagram;
        for (const digest of [artifact, bundle, packetDigest, reportDigest]) assert.match(digest, /^[a-f0-9]{64}$/);
        result.receipt = { artifact, bundle, packetDigest, reportDigest, inputDigest: receipt.inputDigest };
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

    await scenario('portal-affine-sign-change', async () => {
        const { length, height } = portal;
        const top = height / 2, bottom = -height / 2;
        // Vertical translation keeps the physical geometry and fits the blank view.
        await member([0, bottom], [0, top]);
        await member([0, top], [length, top]);
        await member([length, top], [length, bottom]);
        await place('fixed', 0, bottom);
        await place('fixed', length, bottom);
        // Make room for the load label above the top beam before selecting it.
        for (let step = 0; step < 2; step++) {
            await page.getByRole('button', { name: 'Zoom out' }).click();
            canvasScale /= 1.25;
        }
        await affineLoad(top);
        await page.getByLabel('Inspect member').selectOption({ label: 'BC' });
        await generate('portal-affine-sign-change', handReferences.portal, 'BC');

        // Flip and restore the load through the UI. The old diagram must vanish
        // on the edit, and a new Generate is required even after restoring it.
        await selectDistributed();
        await setNumber('fy', 8);
        assert.equal(await diagram.isVisible(), false, 'Old diagram remained visible after the load edit');
        await setNumber('fy', 6);
        assert.equal(await diagram.isVisible(), false, 'Old diagram reappeared after edit and revert');
        await generate('portal-affine-after-revert', handReferences.portal, 'BC');
    });

    await scenario('pin-roller-affine-sign-change', async () => {
        await pinRoller(6);
        await affineLoad(0);
        await generate('pin-roller-affine-sign-change', handReferences.pinRoller, 'AB');
    });

    await scenario('pin-roller-jumps-and-flat-shear', async () => {
        await pinRoller(8);
        await place('force', 2);
        await setNumber('fy', -12);
        await place('moment', 4);
        await setNumber('mz', 6);
        await generate('pin-roller-jumps-and-flat-shear', handReferences.jumps, 'AB');
    });

    await scenario('pin-roller-unloaded', async () => {
        await pinRoller(6);
        await generate('pin-roller-unloaded', handReferences.unloaded, 'AB');
    });

    const result = { records, errors };
    await writeFile(join(output, 'student-member-diagrams.json'), JSON.stringify(result, null, 2) + '\n');
    return result;
}
