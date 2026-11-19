/** Exercise the MAIN diagram and exported receipt using visible drawing
 * controls on a fresh Playwright page. Use synthetic data only.
 */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { compareDiagram, compareRationalToRadical } from './student-canvas-cases.mjs';
import { nodalLoad, distributedLoad } from './member-diagram-joint-references.mjs';

const expectedProtocols = {
    rigid: 'CV2011_FRAME_1', hinge: 'CV2011_HINGE_1',
    spring5000: 'CV2011_ROTATIONAL_SPRING_1', spring2500: 'CV2011_ROTATIONAL_SPRING_1',
};
const memberLabels = { AB: 'A–B', BC: 'B–C' };
const exactAffineCentres = { rigid: [-2, 15], hinge: [38, 15], spring5000: [34, 45], spring2500: [6, 5] };
const hash = value => createHash('sha256').update(value).digest('hex');

/** Compare captured diagram rows with independently derived values and
 * require strict rational enclosure of both irrational moment extrema.
 */
export function compareJointDiagram(observed, family, mode, member) {
    const reference = family === 'affine' ? distributedLoad[mode] : nodalLoad[mode];
    compareDiagram(observed, reference[member]);
    if (family === 'affine' && member === 'AB') independentlyCheckIrrationalBounds(observed.candidates, mode);
}

function readRatio(text) {
    assert.match(text, /^-?\d+\/[1-9]\d*$/);
    return text.split('/').map(BigInt);
}

function containsRational(lower, upper, numerator, denominator) {
    const [lowTop, lowBottom] = readRatio(lower);
    const [highTop, highBottom] = readRatio(upper);
    const top = BigInt(numerator), bottom = BigInt(denominator);
    assert.ok(lowTop * bottom <= top * lowBottom && top * highBottom <= highTop * bottom,
        `Expected ${numerator}/${denominator} within [${lower}, ${upper}]`);
}

function independentlyCheckIrrationalBounds(candidates, mode) {
    const [centreTop, centreBottom] = exactAffineCentres[mode].map(BigInt);
    const aroundCentre = endpoint => {
        const [top, bottom] = readRatio(endpoint);
        return `${top * centreBottom - centreTop * bottom}/${bottom * centreBottom}`;
    };
    const stationaries = candidates.filter(row => row.field === 'M' && row.side === 'interior');
    assert.equal(stationaries.length, 2);
    for (const row of stationaries) {
        const direction = row.max === 'true' ? -1 : 1;
        assert.ok(compareRationalToRadical(row.xLow, [2, direction, 1, 13, 5]) < 0);
        assert.ok(compareRationalToRadical(row.xHigh, [2, direction, 1, 13, 5]) > 0);
        assert.ok(compareRationalToRadical(aroundCentre(row.yLow), [0, -26 * direction, 15, 13, 5]) < 0);
        assert.ok(compareRationalToRadical(aroundCentre(row.yHigh), [0, -26 * direction, 15, 13, 5]) > 0);
    }
}

const springFractions = {
    nodal: {
        spring5000: { 'relative-rotation': [1, 750], 'transmitted-moment': [20, 3],
            'reference-rotation': [-1, 1500], 'end-rotation': [1, 1500] },
        spring2500: { 'relative-rotation': [1, 500], 'transmitted-moment': [5, 1],
            'reference-rotation': [-1, 1000], 'end-rotation': [1, 1000] },
    },
    affine: {
        spring5000: { 'relative-rotation': [-2, 5625], 'transmitted-moment': [-16, 9],
            'reference-rotation': [17, 112500], 'end-rotation': [-23, 112500] },
        spring2500: { 'relative-rotation': [-1, 1875], 'transmitted-moment': [-4, 3],
            'reference-rotation': [3, 12500], 'end-rotation': [-11, 37500] },
    },
};

function checkDrawnSource(model, family, mode) {
    const nodes = new Map(model.nodes.map(node => [node.id, node]));
    const members = new Map(model.members.map(member => [member.id, member]));
    const nodeAt = (member, t) => {
        const a = nodes.get(member.a), b = nodes.get(member.b);
        return a.x + t * (b.x - a.x);
    };
    assert.deepEqual(model.nodes.map(node => [node.x, node.y]).sort((a, b) => a[0] - b[0]),
        [[0, 0], [4, 0], [8, 0]]);
    assert.deepEqual(model.members.map(member => [nodeAt(member, 0), nodeAt(member, 1), member.EI])
        .sort((a, b) => a[0] - b[0]), [[0, 4, 20000], [4, 8, 20000]]);
    assert.deepEqual(model.supports.map(support => [nodeAt(members.get(support.member), support.t), support.kind])
        .sort((a, b) => a[0] - b[0]), [[0, 'fixed'], [8, 'fixed']]);
    const joint = model.nodes.find(node => node.x === 4);
    const jointKind = { rigid: 'rigid', hinge: 'pinned', spring5000: 'semi-rigid', spring2500: 'semi-rigid' };
    assert.equal(joint.joint ?? 'rigid', jointKind[mode]);
    const stiffness = { spring5000: 5000, spring2500: 2500 }[mode];
    if (stiffness) assert.equal(joint.rotationStiffness, stiffness);
    assert.equal(model.loads.length, 1);
    const [load] = model.loads;
    const host = members.get(load.member);
    if (family === 'nodal') {
        assert.deepEqual([load.kind, nodeAt(host, load.t), load.fx, load.fy, load.mz], ['force', 4, 0, -10, 0]);
    } else {
        assert.deepEqual([load.kind, nodeAt(host, load.t), nodeAt(host, load.end), load.fy, load.qEnd],
            ['distributed', 0, 4, -4, 4]);
    }
}

/** Save per-member report rows, course readouts and receipt bindings. The
 * before-and-after records use the same drawing and selected section.
 */
export async function runJointMemberDiagramStudentCases({ page, base, output }) {
    await mkdir(output, { recursive: true });
    const records = [], errors = [];
    page.on('pageerror', error => errors.push(String(error)));
    await page.goto(base);
    const canvas = page.locator('#canvas');
    const inspector = page.locator('#inspector');
    const worked = page.locator('#frame-worked-output');
    const diagram = worked.locator('#checked-member-diagram');
    const field = property => inspector.locator(`[data-property="${property}"]`);
    const tool = name => page.locator(`button[data-tool="${name}"]`).click();
    const closeProperties = page.getByRole('button', { name: 'Close properties' });
    const memberSelect = page.getByLabel('Inspect member');
    const springStiffness = field('rotationStiffness');

    async function setNumber(input, value) {
        await input.fill(String(value));
        await input.press('Tab');
    }

    async function point(x) {
        assert.equal(await closeProperties.isVisible(), false);
        await canvas.scrollIntoViewIfNeeded();
        const position = await canvas.evaluate((svg, x) => {
            // Blank canvas resets to centre (4,0) at 85 SVG units per metre.
            const point = new DOMPoint(500 + (x - 4) * 85, 200).matrixTransform(svg.getScreenCTM());
            return { x: point.x, y: point.y, onCanvas: svg.contains(document.elementFromPoint(point.x, point.y)) };
        }, x);
        assert.ok(position.onCanvas, `Drawing point ${x} did not hit canvas`);
        await page.mouse.click(position.x, position.y);
    }

    async function place(name, x) {
        await tool(name);
        await point(x);
    }

    async function buildDrawing(family) {
        await page.getByLabel('Start from').selectOption({ label: 'Blank canvas' });
        await page.getByRole('button', { name: 'Open example' }).click();
        assert.equal(await canvas.locator('[data-object="member"]').count(), 0);
        const spacing = page.getByLabel('Grid spacing (m)');
        if (!(await spacing.isVisible())) await page.getByText('Snapping', { exact: true }).click();
        await page.getByLabel('Snap to grid and geometry').check();
        await setNumber(spacing, 0.5);
        await place('member', 0);
        await point(4);
        await place('member', 4);
        await point(8);
        await place('fixed', 0);
        await place('fixed', 8);
        if (family === 'nodal') {
            await place('force', 4);
            await setNumber(field('fy'), -10);
        } else {
            await place('distributed', 1);
            await point(3);
            await tool('select');
            await canvas.locator('[data-object="load"]').locator('text').click();
            await setNumber(field('t'), 0);
            await setNumber(field('end'), 1);
            await setNumber(field('fy'), 4);
            await setNumber(field('qEnd'), -4);
        }
    }

    async function setJoint(option) {
        await place('joint', 4);
        await page.getByLabel('Joint connection').selectOption({ label: option });
    }

    async function collect(family, mode, member, phase) {
        const name = `${family}-${mode}-${member}${phase ? '-' + phase : ''}`;
        await memberSelect.selectOption({ label: memberLabels[member] });
        const slider = page.getByRole('slider', { name: 'Section position' });
        await slider.press(member === 'AB' ? 'End' : 'Home');
        await page.getByRole('button', { name: 'Generate worked solution' }).click();
        await diagram.waitFor({ state: 'visible', timeout: 40000 });
        const text = await diagram.innerText();
        const workedText = await worked.innerText();
        const status = await page.locator('#portal-status').innerText();
        const observed = {
            pieces: await diagram.locator('[data-piece]').evaluateAll(nodes => nodes.map(node => ({ ...node.dataset }))),
            candidates: await diagram.locator('[data-candidate]').evaluateAll(nodes => nodes.map(node => ({ ...node.dataset }))),
        };
        assert.match(status, /^Accepted/i);
        assert.ok(text.includes(memberLabels[member]));
        assert.match(text, /V₀.*kN.*M₀.*kN\s*[·⋅]?\s*m.*q₀.*kN\/m.*g.*kN\/m²/);
        compareJointDiagram(observed, family, mode, member);
        if (mode === 'hinge') {
            assert.match(workedText, /released end|released-end rotation/i);
            assert.match(workedText, /moment is zero|M\s*=\s*0/i);
            const face = observed.candidates.find(row => row.field === 'M' && row.side === (member === 'AB' ? 'end' : 'start'));
            assert.deepEqual([face.yLow, face.yHigh], ['0/1', '0/1']);
        }
        const jointValues = {};
        const expectedValues = springFractions[family][mode];
        if (expectedValues) {
            assert.match(workedText, /Δθ/);
            assert.match(workedText, /T\s*=\s*k/);
            assert.match(workedText, /kN\s*[·⋅]?\s*m\/rad/);
            for (const [name, [top, bottom]] of Object.entries(expectedValues)) {
                const readout = worked.locator(`[data-spring-value="${name}"]`);
                assert.ok(await readout.isVisible());
                const lower = await readout.getAttribute('data-lower');
                const upper = await readout.getAttribute('data-upper');
                containsRational(lower, upper, top, bottom);
                jointValues[name] = { lower, upper };
            }
            const face = observed.candidates.find(row => row.field === 'M' && row.side === (member === 'AB' ? 'end' : 'start'));
            const [top, bottom] = expectedValues['transmitted-moment'];
            containsRational(face.yLow, face.yHigh, top, bottom);
        }

        const receipt = JSON.parse(await page.locator('#portal-certificate').textContent());
        assert.equal(receipt.protocol, expectedProtocols[mode]);
        assert.equal(receipt.diagram.protocol, 'CV2011_DIAGRAM_1');
        assert.equal(receipt.sourceRequest.query.member, await memberSelect.inputValue());
        assert.equal(receipt.sourceRequest.query.parameter, member === 'AB' ? 1 : 0);
        checkDrawnSource(receipt.sourceRequest.model, family, mode);
        assert.equal(hash(JSON.stringify(receipt.sourceRequest)), receipt.inputDigest);
        assert.equal(hash(receipt.packet), receipt.packetDigest);
        assert.equal(hash(receipt.packet), receipt.diagram.packetDigest);
        if (receipt.report) assert.equal(hash(receipt.report), receipt.reportDigest);
        assert.equal(hash(receipt.diagram.report), receipt.diagram.reportDigest);
        const { artifact, bundle, packetDigest, reportDigest } = receipt.diagram;
        for (const digest of [artifact, bundle, packetDigest, reportDigest]) assert.match(digest, /^[\da-f]{64}$/);
        const result = { name, status, text, workedText, observed, jointValues,
            receipt: { artifact, bundle, packetDigest, reportDigest, inputDigest: receipt.inputDigest } };
        records.push(result);
        await page.screenshot({ path: join(output, name + '.png'), fullPage: true });
        return result;
    }

    async function bothMembers(family, mode, phase) {
        const results = {};
        for (const member of Object.keys(memberLabels)) {
            results[member] = await collect(family, mode, member, phase);
        }
        return results;
    }

    for (const family of ['nodal', 'affine']) {
        try {
            await buildDrawing(family);
            await bothMembers(family, 'rigid');
            await setJoint('Internal pin / hinge');
            await bothMembers(family, 'hinge');
            await setJoint('Semi-rigid joint');
            await setNumber(springStiffness, 5000);
            const baseline = await bothMembers(family, 'spring5000');
            await place('joint', 4);
            await setNumber(springStiffness, 2500);
            assert.equal(await diagram.isVisible(), false, 'An old diagram remained on the page after a stiffness edit');
            const edited = await bothMembers(family, 'spring2500', 'edited');
            await place('joint', 4);
            await setNumber(springStiffness, 5000);
            assert.equal(await diagram.isVisible(), false, 'An old diagram reappeared on stiffness revert');
            const restored = await bothMembers(family, 'spring5000', 'restored');
            for (const member of Object.keys(memberLabels)) {
                for (const digest of ['inputDigest', 'packetDigest', 'reportDigest']) {
                    assert.notEqual(edited[member].receipt[digest], baseline[member].receipt[digest]);
                }
                assert.deepEqual(restored[member].receipt, baseline[member].receipt);
                assert.deepEqual(restored[member].observed, baseline[member].observed);
            }
        } catch (error) {
            records.push({ name: family, failure: String(error.stack ?? error) });
            await page.screenshot({ path: join(output, family + '-failure.png'), fullPage: true });
        }
    }

    const result = { records, errors };
    await writeFile(join(output, 'student-joint-member-diagrams.json'), JSON.stringify(result, null, 2) + '\n');
    return result;
}
