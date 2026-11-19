/** Replay inclined member diagrams using visible sandbox controls and the
 * original exported receipts. Use with a fresh Playwright page.
 */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { affineInclinedCantilever, inclinedJumpCantilever, inclinedHingeSpan, inclinedSpringSpan, enclosesReference }
    from './member-diagram-inclined-reference.mjs';

const protocol = 'CV2011_INCLINED_DIAGRAM_1';
const ratio = /^-?\d+\/[1-9]\d*$/;
const hash = value => createHash('sha256').update(value).digest('hex');
const position = ([x0, y0], [x1, y1], t) => [x0 + t * (x1 - x0), y0 + t * (y1 - y0)];

/** Decode for QA independently of the TypeScript renderer. */
export function parseInclinedDiagram(report, memberId) {
    const [tag, member, ...records] = report.split('\n');
    assert.equal(tag, protocol);
    assert.equal(member, Array.from({ length: memberId.length }, (_, index) => memberId.charCodeAt(index).toString(16)
        .padStart(4, '0')).join(''));
    const pieces = [], candidates = [];
    for (const record of records) {
        const [field, ...tokens] = record.split(' ');
        if (field === 'P') {
            assert.equal(tokens.length, 10);
            assert.ok(tokens.every(token => ratio.test(token)));
            const [a, b, B, C, lengthLo, lengthHi, vLo, vHi, mLo, mHi] = tokens;
            pieces.push({ a, b, B, C, length: [lengthLo, lengthHi], startShear: [vLo, vHi], startMoment: [mLo, mHi] });
        } else {
            assert.ok(field === 'V' || field === 'M');
            assert.equal(tokens.length, 10);
            const [index, side, tLo, tHi, xLo, xHi, yLo, yHi, min, max] = tokens;
            assert.match(index, /^\d+$/);
            assert.ok(Number(index) < pieces.length);
            assert.ok(['start', 'end', 'flat', 'interior'].includes(side));
            assert.ok([tLo, tHi, xLo, xHi, yLo, yHi].every(token => ratio.test(token)));
            assert.ok([min, max].every(flag => flag === '0' || flag === '1'));
            candidates.push({ field, index: Number(index), side, t: [tLo, tHi], x: [xLo, xHi],
                value: [yLo, yHi], min: min === '1', max: max === '1' });
        }
    }
    return { pieces, candidates };
}

function fractionNumber(value) {
    const [top, bottom] = value.split('/').map(Number);
    return top / bottom;
}

function compareBounds(actual, expected, label, allowSpan = false) {
    assert.ok(enclosesReference(actual, expected), label + ' misses its independent exact bounds');
    const a = actual.map(fractionNumber), b = expected.map(fractionNumber);
    assert.ok(a.every(Number.isFinite) && a[0] <= a[1]);
    const width = allowSpan ? b[1] - b[0] : 0;
    assert.ok(a[1] - a[0] - width < 1e-6, label + ' is wider than the benchmark admits');
}

/** Compare coefficients, side ownership, flags and exact enclosures. */
export function compareInclinedDiagram(observed, expected) {
    const pieces = expected.pieces ?? [expected.piece];
    assert.equal(observed.pieces.length, pieces.length);
    assert.equal(observed.candidates.length, expected.candidates.length);
    for (const [index, ref] of pieces.entries()) {
        const piece = observed.pieces[index];
        assert.equal(piece.a, ref.a);
        assert.equal(piece.b, ref.b);
        compareBounds([piece.B, piece.B], ref.normalizedShear[1], 'B');
        compareBounds([piece.C, piece.C], ref.normalizedShear[2], 'C');
        compareBounds(piece.length, expected.length, 'Member length');
        compareBounds(piece.startShear, ref.normalizedShear[0], 'V0');
        compareBounds(piece.startMoment, ref.normalizedMoment[0], 'M0');
    }
    const endpointFractions = { start: ['0/1', '0/1'], end: ['1/1', '1/1'], flat: ['0/1', '1/1'] };
    for (const ref of expected.candidates) {
        // The wire uses piece-local t. Only the one-piece cantilevers
        // in this replay have interior stationary points.
        const parameter = endpointFractions[ref.side] ?? ref.t;
        const rows = observed.candidates.filter(row => row.field === ref.field && row.index === ref.index &&
            row.side === ref.side && enclosesReference(row.t, parameter));
        assert.equal(rows.length, 1, `Missing or duplicated ${ref.field} ${ref.side} row on piece ${ref.index}`);
        const [row] = rows;
        const label = `${ref.field} ${ref.side} on piece ${ref.index}`;
        compareBounds(row.t, parameter, label + ' (fraction)', ref.side === 'flat');
        compareBounds(row.x, ref.x, label + ' (distance)', ref.side === 'flat');
        compareBounds(row.value, ref.value, label + ' (ordinate)');
        assert.equal(row.min, ref.min, label + ' (minimum flag)');
        assert.equal(row.max, ref.max, label + ' (maximum flag)');
    }
}

export async function runInclinedMemberDiagramStudentCases({ page, base, output }) {
    await mkdir(output, { recursive: true });
    const records = [], errors = [];
    page.on('pageerror', error => errors.push(String(error)));
    await page.goto(base);
    const canvas = page.locator('#canvas');
    const inspector = page.locator('#inspector');
    const diagram = page.locator('#frame-worked-output #checked-member-diagram');
    const selector = page.getByLabel('Inspect member');
    const closeProperties = page.getByRole('button', { name: 'Close properties' });

    async function setNumber(input, value) {
        await input.fill(String(value));
        await input.press('Tab');
    }
    async function number(name, value) {
        await setNumber(inspector.locator(`[data-property="${name}"]`), value);
    }
    async function choose(name) {
        await page.locator(`button[data-tool="${name}"]`).click();
    }
    async function blank() {
        await page.getByLabel('Start from').selectOption({ label: 'Blank canvas' });
        await page.getByRole('button', { name: 'Open example' }).click();
        assert.equal(await canvas.locator('[data-object="member"]').count(), 0);
        const grid = page.getByLabel('Grid spacing (m)');
        if (!(await grid.isVisible())) await page.getByText('Snapping', { exact: true }).click();
        await page.getByLabel('Snap to grid and geometry').check();
        await setNumber(grid, 0.25);
    }
    async function clickPoint(coordinates) {
        assert.equal(await closeProperties.isVisible(), false);
        await canvas.scrollIntoViewIfNeeded();
        const target = await canvas.evaluate((svg, [x, y]) => {
            const point = new DOMPoint(500 + (x - 4) * 85, 200 - y * 85).matrixTransform(svg.getScreenCTM());
            return { x: point.x, y: point.y, onCanvas: svg.contains(document.elementFromPoint(point.x, point.y)) };
        }, coordinates);
        assert.ok(target.onCanvas, `Click at (${coordinates.join(', ')}) must hit the canvas`);
        await page.mouse.click(target.x, target.y);
    }
    async function place(tool, coordinates) {
        await choose(tool);
        await clickPoint(coordinates);
    }
    async function member(first, last) {
        await place('member', first);
        await clickPoint(last);
    }
    async function inspectLoad(index) {
        if (await closeProperties.isVisible()) await closeProperties.click();
        await choose('select');
        await canvas.locator('[data-object="load"]').nth(index).locator('text').click();
        await inspector.getByRole('heading', { name: 'Load properties' }).waitFor();
    }
    async function force(coordinates, parameter, vertical) {
        await place('force', coordinates);
        await number('t', parameter);
        await number('fy', vertical);
    }
    async function couple(coordinates, parameter, value) {
        await place('moment', coordinates);
        await number('t', parameter);
        await number('mz', value);
    }

    async function collect(name, route, memberIndex, expected, auditSource) {
        await selector.selectOption({ index: memberIndex });
        const chosen = await selector.inputValue();
        await page.getByRole('button', { name: 'Generate worked solution' }).click();
        await diagram.waitFor({ state: 'visible', timeout: 40000 });
        const text = await diagram.innerText();
        const status = await page.locator('#portal-status').innerText();
        assert.match(status, /^Accepted/i);
        assert.match(text, /Shear force/i);
        assert.match(text, /Bending moment/i);
        assert.match(text, /kN\s*[·⋅]?\s*m/);
        const receipt = JSON.parse(await page.locator('#portal-certificate').textContent());
        assert.equal(receipt.protocol, route);
        assert.equal(receipt.diagram.protocol, protocol);
        assert.equal(receipt.sourceRequest.query.member, chosen);
        assert.equal(hash(JSON.stringify(receipt.sourceRequest)), receipt.inputDigest);
        assert.equal(hash(receipt.packet), receipt.packetDigest);
        assert.equal(hash(receipt.packet), receipt.diagram.packetDigest);
        assert.equal(hash(receipt.report), receipt.reportDigest);
        assert.equal(hash(receipt.diagram.report), receipt.diagram.reportDigest);
        const { artifact, bundle, packetDigest, reportDigest, report } = receipt.diagram;
        for (const digest of [artifact, bundle, packetDigest, reportDigest]) assert.match(digest, /^[0-9a-f]{64}$/);
        auditSource(receipt.sourceRequest.model, chosen);
        const observed = parseInclinedDiagram(report, chosen);
        compareInclinedDiagram(observed, expected);

        // Confirm that the worked panel displays the interval data it exports.
        const rendered = await diagram.locator('[data-candidate]').evaluateAll(rows => rows.map(row => ({ ...row.dataset })));
        assert.equal(rendered.length, observed.candidates.length);
        for (const row of observed.candidates) {
            const match = rendered.find(item => item.field === row.field && item.side === row.side &&
                Number(item.pieceIndex) === row.index && item.tLow === row.t[0] && item.tHigh === row.t[1]);
            assert.ok(match, 'Missing visible candidate matching the checked receipt');
            assert.deepEqual([match.xLow, match.xHigh], row.x);
            assert.deepEqual([match.yLow, match.yHigh], row.value);
            assert.deepEqual([match.min, match.max], [String(row.min), String(row.max)]);
        }
        const entry = { name, route, status, text, report, observed, member: chosen, rendered,
            receipt: { artifact, bundle, packetDigest, reportDigest, inputDigest: receipt.inputDigest } };
        records.push(entry);
        await page.screenshot({ path: join(output, name + '.png'), fullPage: true });
        return entry;
    }

    function certifySource(model, selected, first, last, expectedLoads, expectedSupports = []) {
        const matches = model.members.find(item => item.id === selected);
        const points = new Map(model.nodes.map(node => [node.id, [node.x, node.y]]));
        assert.deepEqual(points.get(matches.a), first);
        assert.deepEqual(points.get(matches.b), last);
        assert.equal(model.loads.length, expectedLoads.length);
        for (const [index, expected] of expectedLoads.entries()) {
            const load = model.loads[index];
            assert.equal(load.member, selected);
            for (const [key, value] of Object.entries(expected)) assert.equal(load[key], value, 'Source load ' + key);
        }
        if (expectedSupports.length) {
            const actual = model.supports.map(support => {
                const side = model.members.find(item => item.id === support.member);
                return [support.kind, ...position(points.get(side.a), points.get(side.b), support.t)];
            }).sort((a, b) => a[1] - b[1]);
            assert.deepEqual(actual, expectedSupports);
        }
    }

    async function scenario(name, callback) {
        try {
            await blank();
            await callback();
        } catch (error) {
            records.push({ name, failure: String(error.stack ?? error) });
            await page.screenshot({ path: join(output, name + '-failure.png'), fullPage: true });
        }
    }
    for (const [height, reversed] of [[3, false], [2, false], [2, true]]) {
        const name = `rigid-affine-rise-${height}${reversed ? '-reversed' : ''}`;
        await scenario(name, async () => {
            const fixed = [0, -height / 2], free = [4, height / 2];
            const first = reversed ? free : fixed, last = reversed ? fixed : free;
            const tipParameter = reversed ? 0 : 1, wStart = reversed ? -6 : 6;
            await member(first, last);
            await place('fixed', fixed);
            await force(free, tipParameter, -5);
            await place('distributed', position(first, last, .25));
            await clickPoint(position(first, last, .75));
            await inspectLoad(1);
            await number('t', 0);
            await number('end', 1);
            await number('fy', wStart);
            await number('qEnd', -wStart);
            const checkSource = scale => (model, selected) => certifySource(model, selected, first, last, [
                { kind: 'force', t: tipParameter, fy: -5 * scale, fx: 0 },
                { kind: 'distributed', t: 0, end: 1, fy: -wStart * scale, qEnd: wStart * scale },
            ], [['fixed', ...fixed]]);
            const baseline = await collect(name, 'CV2011_INCLINED_1', 0,
                affineInclinedCantilever(height, reversed), checkSource(1));
            if (height === 2 && !reversed) {
                await inspectLoad(1);
                await number('fy', 2 * wStart);
                assert.equal(await diagram.isVisible(), false);
                await number('qEnd', -2 * wStart);
                await inspectLoad(0);
                await number('fy', -10);
                assert.equal(await diagram.isVisible(), false);
                const edited = await collect(name + '-edited', 'CV2011_INCLINED_1', 0,
                    affineInclinedCantilever(height, reversed, 2), checkSource(2));
                for (const key of ['inputDigest', 'packetDigest', 'reportDigest']) {
                    assert.notEqual(edited.receipt[key], baseline.receipt[key]);
                }
            }
        });
    }
    await scenario('rigid-inclined-jumps', async () => {
        const first = [0, -1], last = [4, 1];
        await member(first, last);
        await place('fixed', first);
        await force(position(first, last, .5), .5, -10);
        await couple(position(first, last, .75), .75, 6);
        await collect('rigid-inclined-jumps', 'CV2011_INCLINED_1', 0, inclinedJumpCantilever(),
            (model, chosen) => certifySource(model, chosen, first, last, [
                { kind: 'force', t: .5, fx: 0, fy: -10 }, { kind: 'moment', t: .75, mz: 6 },
            ], [['fixed', ...first]]));
    });
    await scenario('inclined-hinge', async () => {
        const A = [0, 0], B = [4, 0], C = [8, 2];
        await member(A, B);
        await member(B, C);
        await place('fixed', A);
        await place('pin', C);
        await force(position(B, C, .5), .5, -10);
        await place('joint', B);
        await page.getByLabel('Joint connection').selectOption({ label: 'Internal pin / hinge' });
        await collect('inclined-hinge', 'CV2011_INCLINED_RELEASE_1', 1, inclinedHingeSpan(), (model, chosen) => {
            assert.equal(model.nodes.find(node => node.x === B[0] && node.y === B[1]).joint, 'pinned');
            certifySource(model, chosen, B, C, [{ kind: 'force', t: .5, fx: 0, fy: -10 }], [['fixed', ...A], ['pin', ...C]]);
        });
    });
    for (const reversed of [false, true]) {
        const name = 'inclined-spring' + (reversed ? '-reversed' : '');
        await scenario(name, async () => {
            const A = [0, 0], B = [4, 0], C = [8, 2];
            const first = reversed ? C : B, last = reversed ? B : C, tipParameter = reversed ? 0 : 1;
            await member(A, B);
            await member(first, last);
            await place('fixed', A);
            await force(C, tipParameter, -5);
            await couple(C, tipParameter, 30);
            await place('joint', B);
            await page.getByLabel('Joint connection').selectOption({ label: 'Semi-rigid joint' });
            await number('rotationStiffness', 5000);
            const expected = inclinedSpringSpan(reversed);
            await collect(name, 'CV2011_ROTATIONAL_SPRING_1', 1, expected, (model, chosen) => {
                const joint = model.nodes.find(node => node.x === B[0] && node.y === B[1]);
                assert.deepEqual([joint.joint, joint.rotationStiffness], ['semi-rigid', 5000]);
                certifySource(model, chosen, first, last, [
                    { kind: 'force', t: tipParameter, fy: -5, fx: 0 },
                    { kind: 'moment', t: tipParameter, mz: 30 },
                ], [['fixed', ...A]]);
            });
            for (const [key, reference] of [['relative-rotation', expected.relativeRotation], ['transmitted-moment', expected.springMoment]]) {
                const readout = page.locator(`#frame-worked-output [data-spring-value="${key}"]`);
                assert.ok(await readout.isVisible());
                compareBounds([await readout.getAttribute('data-lower'), await readout.getAttribute('data-upper')], reference, key);
            }
        });
    }
    const result = { records, errors };
    await writeFile(join(output, 'student-inclined-member-diagrams.json'), JSON.stringify(result, null, 2) + '\n');
    return result;
}
