/** Blank-canvas browser acceptance for local slope and displacement in MAIN.
 * recreatePacket regenerates the interval packet for a captured cardinal
 * source, using the appropriate existing proposal builder.
 */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { compareDeformationReport, deformationProtocol, parseDeformationReport }
    from './member-diagram-deformation-audit.mjs';
import {
    portalDeformation, pinnedUniformDeformation, repeatedDisplacementRoot,
    cardinalJointDeformation, inclinedCoupleDeformation, inclinedHingeDeformation, unloadedDeformation,
} from './member-diagram-deformation-reference.mjs';

const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const cardinalProtocols = ['CV2011_FRAME_1', 'CV2011_HINGE_1'];

export async function runMemberDeformationStudentCases({ page, base, output, recreatePacket }) {
    await mkdir(output, { recursive: true });
    const records = [], errors = [];
    page.on('pageerror', error => errors.push(String(error)));
    await page.goto(base);
    const canvas = page.locator('#canvas');
    const inspector = page.locator('#inspector');
    const closeProperties = page.getByRole('button', { name: 'Close properties' });
    const memberSelect = page.getByLabel('Inspect member');
    const panel = page.locator('#frame-worked-output [data-member-kinematics]');
    let scale = 85;

    async function number(input, value) {
        await input.fill(String(value));
        await input.press('Tab');
    }
    async function field(name, value) {
        await number(inspector.locator(`[data-property="${name}"]`), value);
    }
    async function choose(tool) {
        await page.locator(`button[data-tool="${tool}"]`).click();
    }
    async function clickPoint(coordinates) {
        assert.equal(await closeProperties.isVisible(), false);
        await canvas.scrollIntoViewIfNeeded();
        const point = await canvas.evaluate((svg, [x, y, scale]) => {
            const screen = new DOMPoint(500 + (x - 4) * scale, 200 - y * scale).matrixTransform(svg.getScreenCTM());
            return { x: screen.x, y: screen.y, onCanvas: svg.contains(document.elementFromPoint(screen.x, screen.y)) };
        }, [...coordinates, scale]);
        assert.ok(point.onCanvas, `Drawing point (${coordinates.join(', ')}) did not hit the canvas`);
        await page.mouse.click(point.x, point.y);
    }
    async function place(tool, coordinates) {
        await choose(tool);
        await clickPoint(coordinates);
    }
    async function member(first, second) {
        await place('member', first);
        await clickPoint(second);
    }
    async function load(name, point, parameter, value) {
        await place(name, point);
        await field('t', parameter);
        await field(name === 'force' ? 'fy' : 'mz', value);
    }
    async function inspectLoad(index) {
        if (await closeProperties.isVisible()) await closeProperties.click();
        await choose('select');
        await canvas.locator('[data-object="load"]').nth(index).locator('text').click();
        await inspector.getByRole('heading', { name: 'Load properties' }).waitFor();
    }
    async function distributed(first, second, index, w0, w1) {
        // Place within the intended member, then enter exact endpoints.
        await place('distributed', first);
        await clickPoint(second);
        await inspectLoad(index);
        await field('t', 0);
        await field('end', 1);
        await field('fy', w0);
        await field('qEnd', w1);
    }
    async function setJoint(connection) {
        await place('joint', [4, 0]);
        await page.getByLabel('Joint connection').selectOption({ label: connection });
    }
    async function blank() {
        await page.getByLabel('Start from').selectOption({ label: 'Blank canvas' });
        await page.getByRole('button', { name: 'Open example' }).click();
        assert.equal(await canvas.locator('[data-object="member"]').count(), 0);
        const grid = page.getByLabel('Grid spacing (m)');
        if (!(await grid.isVisible())) await page.getByText('Snapping', { exact: true }).click();
        await page.getByLabel('Snap to grid and geometry').check();
        await number(grid, 0.5);
        scale = 85;
    }
    async function scenario(name, run) {
        try {
            await blank();
            await run();
        } catch (error) {
            records.push({ name, failure: String(error.stack ?? error) });
            await page.screenshot({ path: join(output, name + '-failure.png'), fullPage: true });
        }
    }

    async function collect(name, index, reference, points) {
        await memberSelect.selectOption({ index });
        const chosen = await memberSelect.inputValue();
        await page.getByRole('button', { name: 'Generate worked solution' }).click();
        await panel.waitFor({ state: 'visible', timeout: 40000 });
        const status = await page.locator('#portal-status').innerText(), text = await panel.innerText();
        assert.match(status, /^Accepted/);
        assert.match(text, /slope/i);
        assert.match(text, /local transverse displacement/i);
        assert.match(text, /counterclockwise|CCW/i);
        const receipt = JSON.parse(await page.locator('#portal-certificate').textContent());
        const { sourceRequest, kinematics } = receipt;
        if (kinematics.protocol !== undefined) assert.equal(kinematics.protocol, deformationProtocol);
        assert.equal(sourceRequest.query.member, chosen);
        const node = id => sourceRequest.model.nodes.find(item => item.id === id);
        const selected = sourceRequest.model.members.find(item => item.id === chosen);
        assert.deepEqual([selected.a, selected.b].map(id => [node(id).x, node(id).y]), points);
        assert.equal(hash(JSON.stringify(sourceRequest)), receipt.inputDigest);
        assert.equal(kinematics.sourceDigest, receipt.inputDigest);
        assert.equal(hash(receipt.packet), receipt.packetDigest);
        assert.equal(kinematics.basePacketDigest, receipt.packetDigest);
        assert.equal(hash(kinematics.packet), kinematics.packetDigest);
        assert.equal(hash(kinematics.report), kinematics.reportDigest);
        if (cardinalProtocols.includes(receipt.protocol)) {
            assert.equal(typeof recreatePacket, 'function', 'Cardinal replay requires original-source packet reproduction');
            const reproduced = await recreatePacket(sourceRequest, kinematics.packet);
            assert.equal(hash(reproduced), kinematics.packetDigest, 'Reproduced original source gives a different packet');
        } else {
            assert.equal(kinematics.packetDigest, receipt.packetDigest);
        }
        const observed = parseDeformationReport(kinematics.report, chosen);
        compareDeformationReport(observed, reference);
        const { artifact, bundle, packetDigest, basePacketDigest, sourceDigest, reportDigest } = kinematics;
        for (const digest of [artifact, bundle, packetDigest, basePacketDigest, sourceDigest, reportDigest])
            assert.match(digest, /^[0-9a-f]{64}$/);
        const entry = { name, status, text, observed, report: kinematics.report, member: chosen, route: receipt.protocol,
            receipt: { artifact, bundle, packetDigest, basePacketDigest, sourceDigest, reportDigest } };
        records.push(entry);
        await page.screenshot({ path: join(output, name + '.png'), fullPage: true });
        return entry;
    }

    await scenario('portal-deformation', async () => {
        const A = [0, -2], B = [0, 2], C = [6, 2], D = [6, -2];
        await member(A, B);
        await member(B, C);
        await member(C, D);
        await place('fixed', A);
        await place('fixed', D);
        for (let i = 0; i < 2; i++) {
            await page.getByRole('button', { name: 'Zoom out' }).click();
            scale /= 1.25;
        }
        await distributed([1, 2], [5, 2], 0, 6, -6);
        const first = await collect('portal-deformation', 1, portalDeformation(), [B, C]);
        await inspectLoad(0);
        await field('fy', 8);
        assert.equal(await panel.isVisible(), false, 'A load edit left old deformations visible');
        await field('qEnd', -8);
        assert.equal(await panel.isVisible(), false);
        const edited = await collect('portal-deformation-edited', 1, portalDeformation(true), [B, C]);
        for (const field of ['sourceDigest', 'basePacketDigest', 'packetDigest', 'reportDigest'])
            assert.notEqual(edited.receipt[field], first.receipt[field]);
    });
    for (const [name, reference, loaded] of [
        ['pinned-uniform-deformation', pinnedUniformDeformation(), true],
        ['unloaded-deformation', unloadedDeformation(), false],
    ]) {
        await scenario(name, async () => {
            const A = [0, 0], B = [6, 0];
            await member(A, B);
            await place('pin', A);
            await place('roller', B);
            if (loaded) await distributed([1, 0], [5, 0], 0, 6, 6);
            await collect(name, 0, reference, [A, B]);
        });
    }
    await scenario('cardinal-joint-deformation', async () => {
        const A = [0, 0], B = [4, 0], C = [8, 0];
        await member(A, B);
        await member(B, C);
        await place('fixed', A);
        await place('fixed', C);
        // Use the snapped joint. Either incident member may own its force.
        await place('force', B);
        await field('fy', -10);
        for (const mode of ['rigid', 'hinge', 'spring5000', 'spring2500']) {
            if (mode === 'hinge') await setJoint('Internal pin / hinge');
            if (mode === 'spring5000') {
                await setJoint('Semi-rigid joint');
                await field('rotationStiffness', 5000);
            }
            if (mode === 'spring2500') {
                await place('joint', B);
                await field('rotationStiffness', 2500);
                assert.equal(await panel.isVisible(), false, 'A stiffness edit left old deformations visible');
            }
            await collect(`cardinal-${mode}-AB`, 0, cardinalJointDeformation(mode, 'AB'), [A, B]);
            await collect(`cardinal-${mode}-BC`, 1, cardinalJointDeformation(mode, 'BC'), [B, C]);
        }
    });
    await scenario('repeated-displacement-root', async () => {
        const A = [0, 0], B = [4, 0];
        await member(A, B);
        await place('fixed', A);
        await load('force', B, 1, -16);
        await load('moment', B, 1, 20);
        await distributed([1, 0], [3, 0], 2, -6, -6);
        await collect('repeated-displacement-root', 0, repeatedDisplacementRoot(), [A, B]);
    });
    for (const spring of [false, true]) {
        for (const reversed of [false, true]) {
            const name = `inclined-${spring ? 'spring' : 'rigid'}-couple${reversed ? '-reversed' : ''}`;
            await scenario(name, async () => {
                const fixed = [0, 0], joint = spring ? [4, 0] : fixed, tip = spring ? [8, 2] : [4, 2];
                const sides = reversed ? [tip, joint] : [joint, tip];
                if (spring) await member(fixed, joint);
                await member(...sides);
                await place('fixed', fixed);
                await load('moment', tip, reversed ? 0 : 1, 20);
                if (spring) {
                    await setJoint('Semi-rigid joint');
                    await field('rotationStiffness', 5000);
                }
                await collect(name, spring ? 1 : 0, inclinedCoupleDeformation(reversed, spring), sides);
            });
        }
    }
    await scenario('inclined-hinge-deformation', async () => {
        const A = [0, 0], B = [4, 0], C = [8, 2];
        await member(A, B);
        await member(B, C);
        await place('fixed', A);
        await place('roller', C);
        await load('force', [6, 1], .5, -10);
        await setJoint('Internal pin / hinge');
        await collect('inclined-hinge-AB', 0, cardinalJointDeformation('hinge', 'AB'), [A, B]);
        await collect('inclined-hinge-BC', 1, inclinedHingeDeformation(), [B, C]);
    });

    const result = { records, errors };
    await writeFile(join(output, 'student-member-kinematics.json'), JSON.stringify(result, null, 2) + '\n');
    return result;
}
