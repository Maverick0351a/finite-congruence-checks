'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const root = path.resolve(__dirname, '..');
const app = require('../space/context-n5.js');
const record = JSON.parse(fs.readFileSync(path.join(root, 'space/n5-context.json'), 'utf8'));
const context = {window: {}};
vm.runInNewContext(fs.readFileSync(path.join(root, 'space/n5-context-data.js'), 'utf8'), context);
assert.deepEqual(JSON.parse(JSON.stringify(context.window.N5_CONTEXT)), record);
const {operations,groupings} = record.claims[0].values;
// Independent oracle: transform each block into a set of output-block labels.
function valid(p) {
  return operations.every(op => [...new Set(p)].every(g =>
    new Set(p.flatMap((b,x) => b === g ? [p[op[x]]] : [])).size === 1));
}
for (const row of record.partition_audit) {
  assert.equal(app.check(row.partition, operations) === null, valid(row.partition));
  assert.equal(row.valid, valid(row.partition));
  assert(!app.groupingResult(row.partition, operations).includes('undefined'));
}
assert.equal(record.partition_audit.filter(r=>r.valid).length,5);
assert.equal(app.label([0,0,1,2]),'{0, 1} | {2} | {3}');
assert(!app.diagram(groupings).includes('undefined'));
const elements = app.graphElements(record), nodes = new Set(elements.filter(e=>!e.data.source).map(e=>e.data.id));
for (const edge of elements.filter(e=>e.data.source)) {
  assert(nodes.has(edge.data.source) && nodes.has(edge.data.target));
  assert(edge.data.label && edge.data.kind);
  if (edge.data.target === 'target') assert.equal(edge.data.kind,'comparison_reference');
  if (edge.data.source === 'paper') assert.equal(edge.data.kind,'illustration');
}
const html = fs.readFileSync(path.join(root, 'space/context-n5.html'),'utf8');
for (const match of html.matchAll(/(?:src|href)="([^"#?]+)"/g)) {
  const ref = match[1];
  if (!/^https?:/.test(ref)) assert(fs.existsSync(path.join(root,'space',ref)), `Missing local asset ${ref}`);
}
assert(html.includes('family 376'));
assert(html.includes('sorry'));
console.log('N5 context: browser data, all 15 grouping checks, typed links, and local assets passed.');
