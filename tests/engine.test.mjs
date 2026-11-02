import test from 'node:test';
import assert from 'node:assert/strict';
import {analyse, example, splitMember} from '../web/engine.ts';
const near = (actual, expected, tolerance=1e-7) => assert.ok(Math.abs(actual-expected)<tolerance*Math.max(1,Math.abs(expected)), `${actual} != ${expected}`);
const sampleAt = (result,x) => result.elements.flatMap(e=>e.samples).reduce((a,b)=>Math.abs(a.x-x)<Math.abs(b.x-x)?a:b);

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
