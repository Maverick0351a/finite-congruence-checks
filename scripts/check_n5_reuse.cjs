'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const root = path.resolve(__dirname,'..');
const ui = require('../space/n5-reuse.js');
const read = filename => JSON.parse(fs.readFileSync(path.join(root,'space',filename),'utf8'));
const record = read('n5-reuse.json');
const runtime = {window:{}};
vm.runInNewContext(fs.readFileSync(path.join(root,'space/n5-reuse-data.js'),'utf8'),runtime);
assert.deepEqual(JSON.parse(JSON.stringify(runtime.window.N5_REUSE)),record,'Browser sidecar must match downloadable JSON');
assert.equal(record.default_transfer,'reverse');
assert.deepEqual(record.transfers.map(t=>t.key),['reverse','rotate']);

// Independent oracle: no input block may have more than one output-block label.
function valid(partition,operations) {
  return operations.every(operation => [...new Set(partition)].every(group =>
    new Set(partition.flatMap((label,x)=>label===group?[partition[operation[x]]]:[])).size===1));
}
function partitions(prefix=[0]) {
  if (prefix.length===4) return [prefix];
  return Array.from({length:Math.max(...prefix)+2},(_,group)=>partitions([...prefix,group])).flat();
}
const universe = partitions();
assert.equal(universe.length,15);
const allClaims = record.transfers.map(t=>t.record.claim);
for (const transfer of record.transfers) {
  assert.deepEqual(read(transfer.download),transfer.record,'Downloads must be the exact explain envelope');
  const claim = transfer.record.claim;
  for (const side of ['source','target']) {
    const operations = claim.values[side].operations;
    const expected = universe.filter(p=>valid(p,operations));
    assert.deepEqual(expected.map(JSON.stringify).sort(),claim.values[side].groupings.map(JSON.stringify).sort());
    for (const p of universe) assert.equal(ui.groupingFailure(p,operations)===null,valid(p,operations));
  }
  for (let rule=0;rule<2;rule++) for (let object=0;object<4;object++) {
    const step = ui.route(claim,rule,object);
    assert.equal(step.agrees,true);
    const diagram = ui.square(step);
    assert(diagram.includes('role="img"') && diagram.includes('The two routes agree.'));
    assert(!diagram.includes('undefined'));
  }
  assert.equal(ui.correspondenceFailure(claim,claim.mapping.rule_target_to_source),null);
  for (let index=0;index<5;index++) {
    const paired = ui.pairedGroups(claim,index);
    for (const targetBlock of paired.target) {
      assert.deepEqual([...targetBlock.source_objects].sort(),[...paired.source[targetBlock.group].objects].sort(),'Matching group letters must denote corresponding members');
    }
    for (const side of ['source','target']) {
      const markup = ui.groupMarkup(paired[side],2,side);
      assert.equal((markup.match(/aria-pressed="true"/g)||[]).length,1);
      assert.equal((markup.match(/data-source-object=/g)||[]).length,4);
      assert(markup.includes('Group A'));
      assert(!markup.includes('undefined'));
    }
  }
  const elements = ui.graphElements(transfer), nodes = new Set(elements.filter(e=>!e.data.source).map(e=>e.data.id));
  assert.equal(nodes.size,4);
  const narrowNodes = ui.graphElements(transfer,286).filter(e=>!e.data.source);
  assert.equal(new Set(narrowNodes.map(e=>e.position.x)).size,1,'Narrow graph must stack nodes');
  assert.equal(new Set(narrowNodes.map(e=>e.position.y)).size,4,'Stacked nodes must have distinct rows');
  assert.deepEqual(narrowNodes.map(e=>e.data.id),['original','mapping','claim','proof']);
  assert.equal(new Set(ui.graphElements(transfer,500).filter(e=>!e.data.source).map(e=>e.position.x)).size,2,'Wide graph must retain the rectangle');
  for (const edge of elements.filter(e=>e.data.source)) {
    assert(nodes.has(edge.data.source)&&nodes.has(edge.data.target));
    assert(edge.data.label);
  }
  assert.equal(ui.proofSteps(transfer).find(s=>s.id==='proof').detail,claim.theorem);
  for (const step of ui.proofSteps(transfer)) assert.equal(new URL(step.url).hostname,'github.com');
}

const grouping = record.controls.find(c=>c.category==='grouping_failure');
assert.deepEqual(ui.groupingFailure(grouping.partition,grouping.operations),{rule:1,pair:[2,3],outputs:[0,1]});
assert.deepEqual(ui.groupingFailure(grouping.partition,grouping.operations),grouping.witness);
const correspondence = record.controls.find(c=>c.category==='correspondence_failure');
const wrong = ui.correspondenceFailure(allClaims[1],correspondence.rule_map);
assert(wrong && !wrong.agrees);
for (const [key,value] of Object.entries(correspondence.witness)) assert.deepEqual(wrong[key],value);
assert.equal(correspondence.family_unchanged,true);
// A rule-name change cannot alter the fixed operation tables used by this oracle.
assert.equal(universe.filter(p=>valid(p,allClaims[1].values.target.operations)).length,5);
for (const control of record.controls) {
  const markup = ui.controlMarkup(control,record.transfers);
  assert(markup.includes(control.title));
  assert(!markup.includes('undefined'));
}
assert(ui.controlMarkup(record.controls.find(c=>c.category==='unsupported_evidence'),record.transfers).includes('does <strong>not</strong> make the N5 statement false'));

const html = fs.readFileSync(path.join(root,'space/context-n5.html'),'utf8');
for (const match of html.matchAll(/(?:src|href)="([^"#?]+)"/g)) {
  if (!/^https?:/.test(match[1])) assert(fs.existsSync(path.join(root,'space',match[1])),`Missing local asset: ${match[1]}`);
}
assert(html.indexOf('n5-reuse-data.js')<html.indexOf('n5-reuse.js'));
for (const control of ['transfer','grouping','object','rule','mistake','evidence']) {
  assert(html.includes(`for="reuse-${control}"`),`Missing accessible label: ${control}`);
}

// Exercise native select event wiring without requiring a canvas or browser library.
// Visual layout, real keyboard focus, and Cytoscape interaction are separate browser checks.
class Element {
  constructor(id) { this.id=id;this.value='';this.hidden=false;this.listeners={};this._html='';this.textContent=''; }
  set innerHTML(value) { this._html=value;const first=value.match(/<option value="([^"]+)"/);if(first)this.value=first[1]; }
  get innerHTML() { return this._html; }
  addEventListener(name,listener) { (this.listeners[name]||=[]).push(listener); }
  change(value) { this.value=value;for(const listener of this.listeners.change||[])listener({target:this}); }
}
const elements = Object.fromEntries([...html.matchAll(/id="([^"]+)"/g)].map(match=>[match[1],new Element(match[1])]));
const context = {window:{N5_REUSE:record},document:{getElementById:id=>elements[id]}};
vm.runInNewContext(fs.readFileSync(path.join(root,'space/n5-reuse.js'),'utf8'),context);
assert.equal(elements['reuse-content'].hidden,false);
assert.equal(elements['reuse-map-unavailable'].hidden,false);
assert.equal(elements['reuse-fit'].disabled,true);
assert.equal(elements['reuse-download'].href,record.transfers[0].download);
assert(elements['reuse-route-text'].textContent.includes('The two routes agree.'));
for (const transfer of record.transfers) {
  elements['reuse-transfer'].change(transfer.key);
  assert.equal(elements['reuse-download'].href,transfer.download);
  assert(elements['reuse-query-command'].textContent.includes(transfer.record.claim.id));
  assert(elements['reuse-query-command'].textContent.includes('--out n5-reuse-query.json\npython scripts/query_context.py check n5-reuse-query.json'));
  for (let i=0;i<5;i++) {
    elements['reuse-grouping'].change(String(i));
    assert(!elements['reuse-target-groups'].innerHTML.includes('undefined'));
  }
  for (let object=0;object<4;object++) for (let rule=0;rule<2;rule++) {
    elements['reuse-object'].change(String(object));
    elements['reuse-rule'].change(String(rule));
    assert(elements['reuse-route-text'].textContent.includes('The two routes agree.'));
  }
  elements['reuse-evidence'].change('proof');
  assert(elements['reuse-evidence-detail'].innerHTML.includes(transfer.record.claim.theorem));
  assert(elements['reuse-evidence-detail'].innerHTML.includes(transfer.links.receipt));
}
for (const control of record.controls) {
  elements['reuse-mistake'].change(control.id);
  assert(elements['reuse-mistake-result'].innerHTML.includes(control.title));
}
console.log('N5 reuse: exact downloads, 15-partition independent oracles, mapping equations, labeled diagrams, three distinct controls, and native selector wiring passed.');
