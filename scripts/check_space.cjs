/* Check the browser's relation/obstruction logic against independently verified data. */
"use strict";
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const root = path.resolve(__dirname, '..');
const data = JSON.parse(fs.readFileSync(path.join(root,'space/data.json'),'utf8'));
const app = require('../space/app.js');
let relations=0, failures=0, certificates=0;
const normal = blocks => blocks.map(b=>[...b].sort((a,b)=>a-b)).sort((a,b)=>a[0]-b[0]);
for(const lattice of data.lattices){
  if(!lattice.witness)continue;
  const example=lattice.witness;
  for(const item of example.congruences.threshold_partitions){
    const actual=app.connectedBlocks(example.vertices,app.thresholdEdges(example.color,lattice.leq,item.element_index));
    assert.deepEqual(normal(actual),normal(item.blocks),`${lattice.id}: relation ${item.element}`);
    relations++;
  }
}
for(const example of data.failure_examples){
  const lattice=data.lattices.find(x=>x.id===example.lattice_id), f=example.failure;
  const groups=app.connectedBlocks(example.vertices,f.marked_pairs);
  const start=groups.find(group=>group.includes(f.endpoints[0]));
  assert.deepEqual(start,f.reachable_from_start);
  assert(!start.includes(f.endpoints[1]),`${lattice.id}: obstruction endpoints must be disconnected`);
  assert(lattice.leq[example.color[f.endpoints[0]][f.endpoints[1]]][f.join_bound]);
  assert.equal(example.verification.passed,false);
  assert.equal(example.verification.checks.seed_connectivity,false);
  const generated=app.graphSvg(example,lattice,f.join_bound,f.marked_pairs);
  const pairs=new Set(f.marked_pairs.filter(([a,b])=>a!==b).map(([a,b])=>[Math.min(a,b),Math.max(a,b)].join(',')));
  assert.equal((generated.match(/<line /g)||[]).length,pairs.size,`${lattice.id}: display only generated edges`);
  assert(!generated.includes('stroke-dasharray'),`${lattice.id}: absent edges must remain absent`);
  failures++;
}
for(const example of [...data.lattices.map(x=>x.witness).filter(Boolean),...data.failure_examples]){
  const bytes=fs.readFileSync(path.join(root,'space',example.certificate));
  assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),example.certificate_sha256);
  certificates++;
}
assert.equal(data.lattices.length,8);assert.equal(relations,31);assert.equal(failures,4);assert.equal(certificates,11);
assert.deepEqual(app.connectedBlocks(3,[]),[[0],[1],[2]]);
assert.deepEqual(app.connectedBlocks(4,[[2,1],[1,0]]),[[0,1,2],[3]]);
assert.equal(app.escapeHtml('<script>"&'), '&lt;script&gt;&quot;&amp;');
assert(data.lattices.find(l=>l.id==='M4').witness===null);
console.log(`Explorer checks passed: ${relations} recorded relations, ${failures} connectivity obstructions, ${certificates} certificate hashes.`);
