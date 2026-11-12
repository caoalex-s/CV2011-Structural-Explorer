import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js')) return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { compileFrame, FrameCandidates, frameQueryConvention } = await import('../web/frame-candidate.ts');
const { framePacket } = await import('../web/frame-packet.ts');
const { decodeAcceptedFramePacket } = await import('../web/frame-result.ts');
const { createFrameWorked, validateFrameWorked } = await import('../web/frame-worked.ts');
const { renderFrameWorked } = await import('../web/frame-worked-view.ts');
const { example } = await import('../web/engine.ts');
const query = (member, parameter = 0.5, cutSide = 'left') => ({ member, parameter, cutSide, ...frameQueryConvention });
// Unit fixtures exercise presentation only. These candidate packets have NOT
// been accepted by Lean; the Linux browser suite supplies actual acceptance.
function fixture(model, selected) {
    const candidate = new FrameCandidates().produce(compileFrame(model, selected));
    const values = decodeAcceptedFramePacket(framePacket(model, selected, candidate));
    return createFrameWorked(model, selected, values, { revision: 7, request: 2,
        bindings: { fixture: true }, artifact: 'unit-fixture', bundle: 'unit-fixture',
        inputDigest: 'unit-fixture', packetDigest: 'unit-fixture' });
}
const beam = () => ({ nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 8, y: 0 }],
    members: [{ id: 'beam', a: 'A', b: 'B', EA: 2000000, EI: 20000 }],
    supports: [0, 0.5, 1].map((t, i) => ({ id: `s${i}`, member: 'beam', t, kind: i ? 'roller' : 'pin', angle: 90 })),
    loads: [{ id: 'load', label: 'w_7', member: 'beam', kind: 'distributed', t: 0, end: 1, fx: 0, fy: -5, mz: 0, qEnd: -5 }] });

test('two-span explanation follows exact source ownership and checked-result references', () => {
    const report = fixture(beam(), query('beam'));
    assert.deepEqual(report.steps.find(step => step.id === 'M').result.value, { numerator: '-10', denominator: '1' });
    assert.deepEqual(report.interval.from, { numerator: '0', denominator: '1' });
    assert.deepEqual(report.interval.to, { numerator: '1', denominator: '2' });
    assert.ok(report.steps.every(step => step.evidence === 'explanatory-rule'));
    assert.ok(report.steps.filter(step => step.result).every(step => step.result.evidence === 'verified-result'));
    const html = renderFrameWorked(report);
    assert.doesNotMatch(html, /math-error/);
    assert.match(html, /w₇/);
    assert.match(html, /Rounded substitution \(explanatory\)/);
    assert.match(html, /not separately Lean-checked/);
});

test('loaded portal uses axial bending particular terms and global orientation', () => {
    const model = example('frame');
    model.nodes[1].y = model.nodes[2].y = 3.25;
    model.nodes[2].x = model.nodes[3].x = 7.5;
    model.members[1].EI = 30000;
    for (const member of model.members) {
        const report = fixture(model, query(member.id, 0.25));
        assert.doesNotMatch(renderFrameWorked(report), /math-error/);
        assert.ok(report.steps.find(step => step.id === 'uy').symbolicExpression.includes('^{4}/24'));
        assert.equal(report.values.query.member, member.id);
    }
});

test('decimal partial overlap and a couple retain exact one-sided interval rules', () => {
    const model = beam();
    model.nodes[1].x = 10; model.supports[1].t = 0.4;
    model.loads[0].t = 0.2; model.loads[0].end = 0.8;
    model.loads.push({ ...model.loads[0], id: 'overlap', label: 'w_8', t: 0.4, end: 1, fy: -2, qEnd: -2 },
        { id: 'couple', member: 'beam', kind: 'moment', t: 0.6, end: 1, fx: 0, fy: 0, mz: 3, qEnd: 0 });
    const left = fixture(model, query('beam', 0.6, 'left'));
    const right = fixture(model, query('beam', 0.6, 'right'));
    assert.notDeepEqual(left.interval.from, right.interval.from);
    assert.deepEqual(left.interval.values.q, { numerator: '-7', denominator: '1' });
    assert.deepEqual(right.interval.values.q, left.interval.values.q);
    assert.doesNotMatch(renderFrameWorked(right), /math-error/);
});

test('unusual source identifiers remain text and load renames rebind presentation', () => {
    const model = beam(), id = '<img src=x onerror=alert(1)>梁';
    model.members[0].id = id;
    [...model.supports, ...model.loads].forEach(item => { item.member = id; });
    const first = fixture(model, query(id));
    model.loads[0].label = 'q_A';
    const renamed = fixture(model, query(id));
    assert.deepEqual(first.values.readouts, renamed.values.readouts);
    const html = renderFrameWorked(renamed);
    assert.doesNotMatch(html, /<img|math-error|w₇/);
    assert.match(html, /&lt;img/);
    assert.match(html, /q_A/);
});

test('tampered intermediate claims, rules, exact substitutions and returned values fail presentation validation', () => {
    const original = fixture(beam(), query('beam'));
    const edits = [
        report => { report.steps[2].evidence = 'verified-result'; },
        report => { report.steps[2].inputs.a1.numerator = '99'; },
        report => { report.steps[2].predicate = 'invented.theorem'; },
        report => { report.steps[2].dependencies = []; },
        report => { report.steps[2].exactSubstitution = '99'; },
        report => { report.steps[2].result.value.numerator = '99'; },
        report => { report.query.cutSide = 'right'; },
    ];
    for (const edit of edits) {
        const report = structuredClone(original); edit(report);
        assert.throws(() => validateFrameWorked(report));
    }
});

test('mechanism has no equilibrium derivation or inherited field badges', () => {
    const model = beam(); model.supports = []; model.loads = [];
    const report = fixture(model, query('beam'));
    assert.deepEqual(report.steps, []);
    const html = renderFrameWorked(report);
    assert.match(html, /No unique equilibrium solution/);
    assert.doesNotMatch(html, /verified-result|Support reactions/);
});
