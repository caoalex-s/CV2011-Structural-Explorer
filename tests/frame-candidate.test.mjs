import test from 'node:test';
import assert from 'node:assert/strict';
import { registerHooks } from 'node:module';
registerHooks({ resolve(specifier, context, next) {
    if (context.parentURL?.includes('/web/') && specifier.startsWith('./') && specifier.endsWith('.js')) return next(specifier.replace(/\.js$/, '.ts'), context);
    return next(specifier, context);
} });
const { compileFrame, FrameCandidates, frameQueryConvention } = await import('../web/frame-candidate.ts');
const { encoded, dot, zero, equal, mul, div, sub, integer, binary64 } = await import('../web/frame-rational.ts');
const { portalCandidate } = await import('../web/portal-candidate.ts');
const { example } = await import('../web/engine.ts');
const query = (member, parameter = 0.5, cutSide = 'left') => ({ member, parameter, cutSide, ...frameQueryConvention });
const udl = (id, member, t = 0, end = 1, fy = -5) => ({ id, member, kind: 'distributed', t, end, fx: 0, fy, mz: 0, qEnd: fy });
const support = (id, member, t, kind = 'roller') => ({ id, member, t, kind, angle: 90 });
function twoSpans(single = false) {
    return single ? {
        nodes: [{ id: 'left', x: 0, y: 0 }, { id: 'right', x: 8, y: 0 }],
        members: [{ id: 'beam', a: 'left', b: 'right', EA: 2000000, EI: 20000 }],
        supports: [support('a', 'beam', 0, 'pin'), support('b', 'beam', 0.5), support('c', 'beam', 1)],
        loads: [udl('w', 'beam')],
    } : {
        nodes: [{ id: 'left', x: 0, y: 0 }, { id: 'middle', x: 4, y: 0 }, { id: 'right', x: 8, y: 0 }],
        members: [{ id: 'first', a: 'left', b: 'middle', EA: 2000000, EI: 20000 },
            { id: 'second', a: 'middle', b: 'right', EA: 2000000, EI: 20000 }],
        supports: [support('a', 'first', 0, 'pin'), support('b', 'first', 1), support('c', 'second', 1)],
        loads: [udl('w1', 'first'), udl('w2', 'second')],
    };
}
function solve(model, selected) {
    const frame = compileFrame(model, selected), candidate = new FrameCandidates().produce(frame);
    assert.equal(candidate.kind, 'solution');
    for (const index of frame.free) assert.ok(equal(dot(frame.stiffness[index], candidate.motion), frame.force[index]));
    for (let i = 0; i < frame.blocked.length; i++) if (frame.blocked[i]) assert.ok(equal(candidate.motion[i], zero));
    return { frame, candidate };
}

test('one- and two-member continuous beams recover the independent textbook baseline', () => {
    for (const single of [false, true]) {
        const { frame, candidate } = solve(twoSpans(single), query(single ? 'beam' : 'first', single ? 0.5 : 1));
        const vertical = frame.supportPoints.map(point => encoded(candidate.reactions[3 * point + 1]));
        assert.deepEqual(vertical, [{ numerator: '15', denominator: '2' }, { numerator: '25', denominator: '1' }, { numerator: '15', denominator: '2' }]);
        assert.deepEqual(encoded(candidate.readouts[2]), { numerator: '-10', denominator: '1' });
        assert.ok(equal(candidate.readouts[5], zero));
    }
});

test('the original portal is a regression of the generic source-driven algorithm', () => {
    const { candidate } = solve(example('frame'), query('BC'));
    const expected = portalCandidate(-5);
    assert.deepEqual(candidate.motion.map(encoded), expected.slice(1, 13));
    assert.deepEqual([0, 1, 2, 9, 10, 11].map(i => encoded(candidate.reactions[i])), expected.slice(13, 19));
    assert.deepEqual(encoded(candidate.readouts[2]), expected[19]);
    assert.deepEqual(encoded(candidate.readouts[5]), expected[20]);
});

test('resized portal, horizontal force and changed restraint use the same candidate producer', () => {
    const model = example('frame');
    model.nodes[1].y = model.nodes[2].y = 3.25;
    model.nodes[2].x = model.nodes[3].x = 7.5;
    model.supports[0].kind = 'pin';
    model.loads.push({ id: 'horizontal', member: 'BC', kind: 'force', t: 0, end: 1, fx: 7, fy: 0, mz: 0, qEnd: 0 });
    const { candidate } = solve(model, query('AB', 0.25));
    assert.equal(candidate.motion.length, 12);
    assert.ok(candidate.readouts.some(value => value.n !== 0n));
});

test('partial overlapping loads, point forces and distinct near-coincident cuts remain exact', () => {
    const model = twoSpans(true);
    model.loads = [udl('w1', 'beam', 0.25, 0.75, -2), udl('w2', 'beam', 0.5, 1, -3),
        { id: 'P', member: 'beam', kind: 'force', t: 0.5000000001, end: 1, fx: 0, fy: -1, mz: 0, qEnd: 0 }];
    const frame = compileFrame(model, query('beam', 0.5, 'right'));
    assert.equal(frame.points.length, 6);
    assert.equal(frame.segments.length, 5);
    const covered = frame.segments.find(segment => equal(segment.from, binary64(0.5)));
    assert.deepEqual(encoded(covered.vertical), { numerator: '-5', denominator: '1' });
    assert.ok(frame.segments.some(segment => segment.length.n > 0n && Number(segment.length.n) / Number(segment.length.d) < 1e-8));
});

test('factor cache respects load, boundary and dimension changes', () => {
    const model = example('frame'), producer = new FrameCandidates();
    const first = compileFrame(model, query('BC')), baseline = producer.produce(first);
    model.loads[0].fy = model.loads[0].qEnd = -12;
    const second = compileFrame(model, query('BC')), edited = producer.produce(second);
    assert.equal(first.boundaryKey, second.boundaryKey);
    baseline.motion.forEach((value, i) => assert.ok(equal(edited.motion[i], div(mul(value, integer(12)), integer(5)))));
    model.supports[0].kind = 'pin';
    const third = compileFrame(model, query('BC'));
    assert.notEqual(second.boundaryKey, third.boundaryKey);
    assert.equal(producer.produce(third).kind, 'solution');
    model.nodes[1].y = model.nodes[2].y = 3.25;
    assert.notEqual(third.structuralKey, compileFrame(model, query('BC')).structuralKey);
});

test('zero-load mechanisms require a nonzero exact null candidate', () => {
    const model = twoSpans();
    model.supports = []; model.loads = [];
    const frame = compileFrame(model, query('first')), candidate = new FrameCandidates().produce(frame);
    assert.equal(candidate.kind, 'mechanism');
    assert.ok(candidate.motion.some(value => value.n !== 0n));
    for (const row of frame.stiffness) assert.ok(equal(dot(row, candidate.motion), zero));
    assert.ok(equal(candidate.loadWork, zero));
});

test('fully restrained loaded members retain the load particular displacement', () => {
    const model = twoSpans(true);
    model.supports = [support('a', 'beam', 0, 'fixed'), support('b', 'beam', 1, 'fixed')];
    const { candidate } = solve(model, query('beam'));
    assert.deepEqual(candidate.motion.map(encoded), Array(6).fill({ numerator: '0', denominator: '1' }));
    assert.equal(candidate.diagonal.length, 0);
    assert.ok(candidate.readouts[5].n < 0n);
});

test('unsupported geometry and restraint semantics are never rounded into the class', () => {
    for (const edit of [m => { m.nodes[1].x += 0.001; }, m => { m.supports[0].kind = 'roller'; m.supports[0].angle = 89.999999999; },
        m => { m.nodes[1].joint = 'pinned'; }, m => { m.loads[0].qEnd = -6; }]) {
        const model = example('frame'); edit(model);
        assert.throws(() => compileFrame(model, query('BC')), /Unsupported/);
    }
    assert.throws(() => binary64(Number.MIN_VALUE), /Limit/);
    assert.deepEqual(encoded(binary64(0.1)), { numerator: '3602879701896397', denominator: '36028797018963968' });
});

test('endpoint queries reject the exterior side and retain interior point-action jumps', () => {
    const model = twoSpans(true);
    assert.throws(() => compileFrame(model, query('beam', 0, 'left')), /interior limit/);
    assert.throws(() => compileFrame(model, query('beam', 1, 'right')), /interior limit/);
    solve(model, query('beam', 0, 'right'));
    solve(model, query('beam', 1, 'left'));
    model.loads.push({ id: 'P', member: 'beam', kind: 'force', t: 0.25, end: 1, fx: 0, fy: -7, mz: 0, qEnd: 0 });
    const left = solve(model, query('beam', 0.25, 'left')).candidate.readouts;
    const right = solve(model, query('beam', 0.25, 'right')).candidate.readouts;
    assert.ok(equal(sub(right[1], left[1]), integer(-7)));
    assert.ok(equal(left[2], right[2]));
});
