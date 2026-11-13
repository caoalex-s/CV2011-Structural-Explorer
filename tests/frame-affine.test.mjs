import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js'))
        return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { compileFrame, FrameCandidates, frameQueryConvention } = await import('../web/frame-candidate.ts');
const { encoded, equal, add, sub, mul, neg, integer, zero } = await import('../web/frame-rational.ts');
const { example, analyse } = await import('../web/engine.ts');
const { framePacket } = await import('../web/frame-packet.ts');
const { decodeAcceptedFramePacket } = await import('../web/frame-result.ts');
const { createFrameWorked } = await import('../web/frame-worked.ts');
const { renderFrameWorked } = await import('../web/frame-worked-view.ts');
const query = (member = 'beam', parameter = 0.5, cutSide = 'left') => ({ member, parameter, cutSide, ...frameQueryConvention });
const beam = () => ({ nodes: [{ id: 'A', x: 0, y: 0 }, { id: 'B', x: 6, y: 0 }],
    members: [{ id: 'beam', a: 'A', b: 'B', EA: 2000000, EI: 20000 }],
    supports: [{ id: 'a', member: 'beam', t: 0, kind: 'pin', angle: 90 },
        { id: 'b', member: 'beam', t: 1, kind: 'roller', angle: 90 }],
    loads: [{ id: 'w', member: 'beam', kind: 'distributed', t: 0, end: 1, fx: 0, fy: -5, qEnd: 5, mz: 0 }] });
function solve(model, selected = query()) {
    const frame = compileFrame(model, selected);
    return { frame, result: new FrameCandidates().produce(frame) };
}
const numeric = value => Number(value.n) / Number(value.d);

test('zero resultant retains the load couple and opposite signed reactions', () => {
    const { frame, result } = solve(beam());
    assert.equal(frame.segments.length, 1, 'zero crossing does not create an artificial cut');
    assert.deepEqual([result.reactions[1], result.reactions[4]].map(encoded),
        [{ numerator: '5', denominator: '1' }, { numerator: '-5', denominator: '1' }]);
    assert.ok(equal(add(frame.force[1], frame.force[4]), zero));
    assert.ok(equal(add(add(frame.force[2], frame.force[5]), mul(integer(6), frame.force[4])), integer(30)));
    const left = solve(beam(), query('beam', 0.5, 'left')).result.readouts;
    const right = solve(beam(), query('beam', 0.5, 'right')).result.readouts;
    assert.deepEqual(left, right);
    assert.ok(equal(left[2], zero));
    assert.ok(equal(left[5], zero));
});

test('triangular and trapezoidal source loads retain analytic resultant and first moment', () => {
    for (const [start, end] of [[0, -6], [-2, -8], [-5, 5]]) {
        const model = beam(); model.loads[0].fy = start; model.loads[0].qEnd = end;
        const { frame } = solve(model);
        assert.equal(numeric(add(frame.force[1], frame.force[4])), 3 * (start + end));
        assert.equal(numeric(add(add(frame.force[2], frame.force[5]), mul(integer(6), frame.force[4]))), 6 * (start + 2 * end));
    }
});

test('partial overlapping affine loads restrict both endpoints exactly', () => {
    const model = beam();
    model.loads[0].t = 0.25; model.loads[0].end = 0.75;
    model.loads[0].fy = -4; model.loads[0].qEnd = 4;
    model.loads.push({ ...model.loads[0], id: 'overlap', t: 0.5, end: 1, fy: 2, qEnd: -2 });
    const { frame } = solve(model);
    assert.deepEqual(frame.segments.map(s => [numeric(s.vertical), numeric(s.verticalEnd)]),
        [[0, 0], [-4, 0], [2, 4], [0, -2]]);
    // Every cut without a point force or couple retains continuous section values.
    for (const t of [0.25, 0.5, 0.75]) {
        assert.deepEqual(solve(model, query('beam', t, 'left')).result.readouts,
            solve(model, query('beam', t, 'right')).result.readouts);
    }
});

test('member reversal preserves global motion/reactions and reverses signed local section forces', () => {
    const original = beam(), reversed = beam();
    [reversed.members[0].a, reversed.members[0].b] = [reversed.members[0].b, reversed.members[0].a];
    reversed.supports.forEach(s => { s.t = 1 - s.t; });
    [reversed.loads[0].fy, reversed.loads[0].qEnd] = [reversed.loads[0].qEnd, reversed.loads[0].fy];
    const forward = solve(original, query('beam', 0.25, 'left')).result;
    const backward = solve(reversed, query('beam', 0.75, 'right')).result;
    assert.deepEqual(forward.motion, backward.motion);
    assert.deepEqual(forward.reactions, backward.reactions);
    assert.deepEqual(forward.readouts.slice(3), backward.readouts.slice(3));
    assert.ok(equal(forward.readouts[0], backward.readouts[0]));
    assert.ok(equal(forward.readouts[1], backward.readouts[1]));
    assert.ok(equal(forward.readouts[2], neg(backward.readouts[2])));
});

test('fully restrained axial and bending fields retain affine particular motion', () => {
    for (const vertical of [false, true]) {
        const model = beam(); model.supports.forEach(s => { s.kind = 'fixed'; });
        if (vertical) { model.nodes[1].x = 0; model.nodes[1].y = 6; }
        const result = solve(model, query('beam', 0.25)).result;
        assert.ok(result.motion.every(value => equal(value, zero)));
        assert.notEqual(result.readouts[5].n, 0n);
        if (!vertical) assert.notEqual(result.readouts[3].n, 0n);
    }
});

test('synthetic screenshot-like portal balances signed reactions and renders affine rules', () => {
    // Public example dimensions, not a reconstruction of the unknown screenshot model.
    const model = example('frame'); model.loads[0].fy = -5; model.loads[0].qEnd = 5;
    const selected = query('BC', 0.25), { result } = solve(model, selected);
    assert.ok(result.reactions[1].n > 0n && result.reactions[10].n < 0n);
    assert.ok(equal(add(result.reactions[1], result.reactions[10]), zero));
    const floating = analyse(model);
    for (const reaction of floating.reactions) {
        const index = model.nodes.findIndex(node => node.x === reaction.x && node.y === reaction.y);
        assert.ok(Math.abs(numeric(result.reactions[3 * index + 1]) - reaction.fy) < 1e-7);
    }
    // Unit fixture only: native/WASM acceptance is checked separately in CI.
    const values = decodeAcceptedFramePacket(framePacket(model, selected, result));
    const report = createFrameWorked(model, selected, values, { revision: 1, request: 1,
        bindings: {}, artifact: 'unit-fixture', bundle: 'unit-fixture', inputDigest: 'unit-fixture', packetDigest: 'unit-fixture' });
    const html = renderFrameWorked(report);
    assert.doesNotMatch(html, /math-error/);
    assert.match(html, /upward-positive intensity = -5 to 5/);
    assert.match(html, /drawing w = 5 to -5/);
    assert.ok(report.steps.find(step => step.id === 'uy').symbolicExpression.includes('^{5}/120'));
    assert.ok(report.steps.every(step => step.evidence === 'explanatory-rule'));
});
