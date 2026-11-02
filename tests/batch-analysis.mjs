// JSON bridge for independent Python/SymPy comparison against the TS solver.
import {readFileSync} from 'node:fs';
import {analyse} from '../web/engine.ts';
const models=JSON.parse(readFileSync(0,'utf8'));
console.log(JSON.stringify(models.map(model=>{
  const result=analyse(model);
  return {status:result.status,reactions:result.reactions,sections:result.elements.map(element=>element.samples[20])};
})));
