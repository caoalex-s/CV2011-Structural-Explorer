import test from 'node:test';
import assert from 'node:assert/strict';
import {analyse, example, splitMember, nodeLabel, nodeLabels} from '../web/engine.ts';
import {forceGeometry, momentGeometry} from '../web/symbols.ts';
const near = (actual, expected, tolerance=1e-7) => assert.ok(Math.abs(actual-expected)<tolerance*Math.max(1,Math.abs(expected)), `${actual} != ${expected}`);
const sampleAt = (result,x) => result.elements.flatMap(e=>e.samples).reduce((a,b)=>Math.abs(a.x-x)<Math.abs(b.x-x)?a:b);

test('internal hinge transfers shear, releases moment, and permits a slope jump', () => {
  const result = analyse(example('hinge'));
  assert.equal(result.status, 'stable');
  assert.equal(result.degree, 0);
  near(result.reactions[0].fy, 10);
  near(result.reactions[0].mz, 40);
  near(result.reactions[1].fy, 10);
  const left = result.elements.find(element => element.member === 'AB').samples.at(-1);
  const right = result.elements.find(element => element.member === 'BC').samples[0];
  near(left.M, 0); near(right.M, 0); near(left.uy, right.uy);
  assert.ok(Math.abs(left.rotation - right.rotation) > 1e-4);
});

test('rotational spring adds the analytical tip displacement P b² / kθ', () => {
  const model = example('semi-rigid'), result = analyse(model);
  assert.equal(result.status, 'stable'); assert.equal(result.degree, 0);
  near(sampleAt(result, 8).uy, -20 * 8 ** 3 / (3 * 20000) - 20 * 4 ** 2 / 10000);
  const connection = result.connections[0];
  near(connection.relativeRotation, -80 / 10000);
  near(connection.moment, 10000 * connection.relativeRotation);
  near(result.reactions[0].mz, 160);
  model.nodes[1].joint = 'pinned';
  assert.equal(analyse(model).status, 'unstable');
  model.nodes[1].joint = 'rigid';
  near(sampleAt(analyse(model), 8).uy, -20 * 8 ** 3 / (3 * 20000));
});

test('axial and transverse joint springs contribute their own relative displacements', () => {
  const model = example('semi-rigid'); model.nodes[1].joint = 'custom';
  model.members[1].connectionA = { axial: 1000, transverse: 'rigid', rotation: 'rigid' };
  model.loads[0].fx = 10; model.loads[0].fy = 0;
  const axial = analyse(model);
  near(sampleAt(axial, 8).ux, 10 * 8 / 2000000 + 10 / 1000);
  near(axial.connections[0].axialForce, 1000 * axial.connections[0].axialSlip);
  model.members[1].connectionA = { axial: 'rigid', transverse: 1000, rotation: 'rigid' };
  model.loads[0].fx = 0; model.loads[0].fy = -20;
  const transverse = analyse(model);
  near(sampleAt(transverse, 8).uy, -20 * 8 ** 3 / (3 * 20000) - 20 / 1000);
  near(transverse.connections[0].transverseForce, 1000 * transverse.connections[0].transverseSlip);
  model.members[1].connectionA.transverse = 'free';
  assert.equal(analyse(model).status, 'unstable');
});

test('local connection directions rotate with the member', () => {
  const model = example('semi-rigid'); model.nodes[1].joint = 'custom';
  model.members[1].connectionA = { axial: 1000, transverse: 'rigid', rotation: 'rigid' };
  model.nodes.forEach(node => { node.y = node.x; node.x = 0; });
  model.loads[0].fy = 10;
  const result = analyse(model);
  near(result.elements.at(-1).samples.at(-1).uy, 10 * 8 / 2000000 + 10 / 1000);
  near(result.reactions[0].fy, -10);
});

test('mixed T joint keeps the beam continuous while the branch has zero end moment', () => {
  const result = analyse(example('mixed'));
  assert.equal(result.status, 'stable');
  const beamLeft = result.elements.find(element => element.member === 'AB').samples.at(-1);
  const beamRight = result.elements.find(element => element.member === 'BC').samples[0];
  const branch = result.elements.find(element => element.member === 'BD').samples[0];
  near(beamLeft.M, beamRight.M); near(beamLeft.rotation, beamRight.rotation);
  assert.ok(Math.abs(beamLeft.M) > 1);
  near(branch.M, 0);
  near(result.reactions.reduce((sum, reaction) => sum + reaction.fy, 0), 20);
});

test('sliding joint transmits transverse force without axial force or moment', () => {
  const result = analyse(example('sliding'));
  assert.equal(result.status, 'stable'); assert.equal(result.degree, 1);
  const connection = result.connections[0];
  near(connection.axialForce, 0); near(connection.moment, 0);
  assert.ok(Math.abs(connection.transverseForce) > 1);
});

test('a couple at a released end acts on the selected member side', () => {
  const model = example('hinge');
  model.loads = [{ ...model.loads[0], kind: 'moment', t: 0, mz: 24 }];
  const result = analyse(model);
  near(result.reactions[0].fy, 6); near(result.reactions[0].mz, 24);
  near(result.reactions[1].fy, -6);
  near(result.elements.find(element => element.member === 'AB').samples.at(-1).M, 0);
  near(result.elements.find(element => element.member === 'BC').samples[0].M, -24);
});

test('custom ground constraints reproduce a fixed support and a guide allows only tangential translation', () => {
  const model = example('cantilever');
  model.supports[0] = { ...model.supports[0], kind: 'custom', fixX: true, fixY: true, fixRotation: true };
  near(analyse(model).reactions[0].mz, 160);
  model.supports[0] = { ...model.supports[0], kind: 'guided', angle: 90 };
  assert.equal(analyse(model).status, 'unstable');
  model.supports.push({ id: 'horizontal', member: 'AB', t: 1, kind: 'roller', angle: 0 });
  const result = analyse(model);
  assert.equal(result.status, 'stable'); near(result.reactions[0].mz, 160);
});

test('splitting a connected member preserves its remote end connection', () => {
  const model = example('semi-rigid');
  const before = analyse(model);
  splitMember(model, 'BC', 0.5, 'new');
  const after = analyse(model);
  near(sampleAt(after, 8).uy, sampleAt(before, 8).uy);
  near(after.connections[0].relativeRotation, before.connections[0].relativeRotation);
});

test('automatic tutorial labels remain unique beyond Z without changing model IDs', () => {
  assert.equal(nodeLabel(0), 'A'); assert.equal(nodeLabel(25), 'Z');
  assert.equal(nodeLabel(26), 'AA'); assert.equal(nodeLabel(51), 'AZ'); assert.equal(nodeLabel(52), 'BA');
  const model = example(); model.nodes[0].id = 'uuid-node';
  assert.equal(nodeLabels(model).get('uuid-node'), 'A');
  const split = example(); splitMember(split, 'AB', 0.4, 'inserted');
  assert.equal(nodeLabels(split).get('inserted'), 'B');
  assert.equal(nodeLabels(split).get('B'), 'C');
});

test('force arrows keep the exact line of action for all vector quadrants', () => {
  for (const [fx, fy] of [[3, 4], [-3, 4], [3, -4], [-3, -4], [0, 5], [5, 0]]) {
    const arrow = forceGeometry(140, 170, fx, fy, 42, 44);
    for (const point of [arrow.tail, arrow.tip]) {
      // Convert the screen offset back to physical y-up coordinates.
      near((point.x - arrow.origin.x) * fy + (point.y - arrow.origin.y) * fx, 0);
    }
    assert.ok((arrow.tip.x - arrow.tail.x) * fx - (arrow.tip.y - arrow.tail.y) * fy > 0);
  }
});

test('moment arcs are concentric with the application point and their tangents have the correct sense', () => {
  for (const moment of [-25, 25]) {
    const arc = momentGeometry(140, 170, moment, 37);
    near(Math.hypot(arc.start.x - arc.center.x, arc.start.y - arc.center.y), 37);
    near(Math.hypot(arc.end.x - arc.center.x, arc.end.y - arc.center.y), 37);
    const cross = -(arc.end.x - arc.center.x) * arc.tangent.y + (arc.end.y - arc.center.y) * arc.tangent.x;
    assert.equal(Math.sign(cross), Math.sign(moment));
  }
});

test('simply supported point load: reactions, moment, and exact deflection',()=>{
  const result=analyse(example()); assert.equal(result.status,'stable'); assert.equal(result.degree,0);
  result.reactions.forEach(r=>near(r.fy,10));
  const middle=sampleAt(result,4); near(middle.M,40); near(middle.uy,-20*8**3/(48*20000)); near(middle.N,0);
});
test('cantilever point load: fixed moment and tip deflection',()=>{
  const result=analyse(example('cantilever')); near(result.reactions[0].mz,160);
  near(sampleAt(result,0).M,-160); near(sampleAt(result,8).uy,-20*8**3/(3*20000));
});
test('UDL recovery includes quartic displacement inside a single element',()=>{
  const result=analyse(example('udl')); result.reactions.forEach(r=>near(r.fy,20));
  near(sampleAt(result,4).M,40); near(sampleAt(result,4).uy,-5*5*8**4/(384*20000));
});
test('triangular load and partial loads preserve global equilibrium',()=>{
  const model=example('udl'); model.loads[0].fy=0; model.loads[0].qEnd=-6;
  const result=analyse(model); near(result.reactions[0].fy,8); near(result.reactions[1].fy,16);
  model.loads[0].t=0.25; model.loads[0].end=0.75; model.loads[0].fy=-6;
  const partial=analyse(model); near(partial.reactions[0].fy,12); near(partial.reactions[1].fy,12);
});
test('interior supports create overhangs without hinges',()=>{
  const result=analyse(example('overhang')); near(result.reactions[0].fy,-20/3); near(result.reactions[1].fy,80/3);
  const all=result.elements.flatMap(e=>e.samples); const support=all.find(p=>Math.abs(p.x-6.4)<1e-7);
  near(support.M,-32); near(support.uy,0);
});
test('a pure couple creates the correct moment jump',()=>{
  const model=example(); model.loads[0].kind='moment'; model.loads[0].mz=30;
  const result=analyse(model); near(result.reactions[0].fy,30/8); near(result.reactions[1].fy,-30/8);
  near(result.elements[1].samples[0].M-result.elements[0].samples.at(-1).M,-30);
});
test('axial force and displacement of a cantilever',()=>{
  const model=example('cantilever'); model.loads[0].fx=30; model.loads[0].fy=0;
  const result=analyse(model); near(sampleAt(result,8).N,30); near(sampleAt(result,8).ux,30*8/2000000);
});
test('two vertical rollers leave a mechanism even under purely vertical load',()=>{
  const model=example(); model.supports[0].kind='roller';
  assert.equal(analyse(model).status,'unstable'); assert.ok(analyse(model).mechanism.length);
});
test('inclined roller enforces its actual reaction direction',()=>{
  const model=example(); model.supports[1].angle=45;
  const result=analyse(model); near(result.reactions[1].fx,10); near(result.reactions[1].fy,10); near(result.reactions[0].fx,-10);
});
test('fixed-fixed UDL and rigid portal frame',()=>{
  const model=example('udl'); model.supports.forEach(s=>s.kind='fixed');
  const result=analyse(model); assert.equal(result.degree,3); near(sampleAt(result,0).M,-5*64/12);
  near(sampleAt(result,4).uy,-5*8**4/(384*20000)); assert.equal(analyse(example('frame')).status,'stable');
});
test('splitting a member remaps loads without changing the solution',()=>{
  const model=example('udl'); const before=analyse(model);
  splitMember(model,'AB',0.35,'C'); const after=analyse(model);
  near(after.reactions[0].fy,before.reactions[0].fy); near(after.reactions[1].fy,before.reactions[1].fy);
  assert.equal(after.degree,0);
});
test('rotating the structure and its load preserves response in member coordinates',()=>{
  const model=example('cantilever'); model.nodes[1]={id:'B',x:0,y:8}; model.loads[0].fy=0; model.loads[0].fx=20;
  const result=analyse(model); const tip=result.elements.at(-1).samples.at(-1);
  near(tip.ux,20*8**3/(3*20000)); near(tip.uy,0); near(result.elements[0].samples[0].M,-160);
});
test('a disconnected unsupported member cannot inherit another component restraints',()=>{
  const model=example(); model.nodes.push({id:'C',x:0,y:4},{id:'D',x:8,y:4});
  model.members.push({id:'CD',a:'C',b:'D',EA:2000000,EI:20000}); assert.equal(analyse(model).status,'unstable');
});
