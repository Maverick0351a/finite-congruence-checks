/* Check rendered mathematical labels and demonstrations using a separate oracle. */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const crypto = require('node:crypto');
const root = path.resolve(__dirname, '..');
const app = require('../space/atlas.js');
const data = JSON.parse(fs.readFileSync(path.join(root, 'space/atlas-data.json'), 'utf8'));
const wrapperContext = { window: {} };
vm.runInNewContext(fs.readFileSync(path.join(root, 'space/atlas-data.js'), 'utf8'), wrapperContext);
assert.deepEqual(JSON.parse(JSON.stringify(wrapperContext.window.ATLAS_DATA)), data, 'Offline JS and JSON must contain identical data.');
const registry = JSON.parse(fs.readFileSync(path.join(root, 'space/atlas-claims.json'), 'utf8'));
vm.runInNewContext(fs.readFileSync(path.join(root, 'space/atlas-claims.js'), 'utf8'), wrapperContext);
assert.deepEqual(JSON.parse(JSON.stringify(wrapperContext.window.ATLAS_CLAIMS)), registry, 'Offline claims JS and JSON must contain identical data.');
assert.deepEqual(registry, JSON.parse(fs.readFileSync(path.join(root, 'evidence/atlas-claims.json'), 'utf8')), 'Browser claims must match the evidence registry.');
const sourceDocuments = new Map(), sourceHashes = new Map();
for (const source of Object.values(registry.sources)) {
  const bytes = fs.readFileSync(path.join(root, source.path), 'utf8').replace(/\r\n/g, '\n');
  const digest = crypto.createHash('sha256').update(bytes, 'utf8').digest('hex');
  assert.equal(source.sha256, digest, source.path + ': claim source hash');
  sourceHashes.set(source.path, digest);
  if (source.path.endsWith('.json')) sourceDocuments.set(source.path, JSON.parse(bytes));
}
assert.deepEqual(sourceDocuments.get('evidence/atlas.json'), data, 'The gallery and cited atlas must agree.');
function resolvePointer(document, pointer) {
  assert(pointer.startsWith('/'), 'Citation must contain a JSON pointer.');
  return pointer.slice(1).split('/').reduce((value, key) => value[key.replace(/~1/g, '/').replace(/~0/g, '~')], document);
}
// Enumerate every assignment of group labels; retain exactly canonical labels.
// This intentionally differs from the UI's recursive partition generator.
function allPartitions(n) {
  const result = [];
  for (let code = 0; code < n ** n; code++) {
    let value = code;
    const assignment = Array.from({ length: n }, () => { const digit = value % n; value = Math.floor(value / n); return digit; });
    const names = new Map();
    const canonical = assignment.map(label => { if (!names.has(label)) names.set(label, names.size); return names.get(label); });
    if (assignment.every((label, i) => label === canonical[i])) result.push(assignment);
  }
  return result;
}
function preserves(partition, op) {
  return partition.every((group, i) => partition.every((other, j) => group !== other || partition[op[i]] === partition[op[j]]));
}
function label(partition) {
  const seen = [];
  for (let i = 0; i < partition.length; i++) {
    let group = seen.find(g => partition[g[0]] === partition[i]);
    if (!group) { group = []; seen.push(group); }
    group.push(i);
  }
  return seen.map(group => group.map(i => String.fromCharCode(65 + i)).join('')).join(' | ');
}
let demonstrations = 0, failures = 0, renderedNodes = 0, renderedEdges = 0, entryClaimLinks = 0;
for (const entry of data.entries) {
  const partitions = allPartitions(entry.carrier_size);
  assert.deepEqual(app.partitions(entry.carrier_size).map(p => p.join(',')).sort(), partitions.map(p => p.join(',')).sort());
  const trueFamily = partitions.filter(p => entry.operations.every(op => preserves(p, op)));
  assert.deepEqual(trueFamily.map(p => p.join(',')).sort(), entry.partitions.map(p => p.join(',')).sort(), entry.id + ': complete displayed family');
  for (const p of partitions) {
    const valid = entry.operations.every(op => preserves(p, op)), result = app.checkGrouping(p, entry.operations);
    assert.equal(result.valid, valid, entry.id + ': grouping verdict');
    assert.equal(app.partitionLabel(p), label(p));
    const text = app.groupingHtml(p, entry.operations);
    assert(text.includes(valid ? 'This grouping works.' : 'This grouping fails.'));
    if (!valid) {
      const { operation, inputs: [a, b], outputs: [fa, fb] } = result.witness;
      assert.equal(p[a], p[b]);
      assert.equal(entry.operations[operation][a], fa);
      assert.equal(entry.operations[operation][b], fb);
      assert.notEqual(p[fa], p[fb]);
      assert(text.includes(`${String.fromCharCode(65 + a)} and ${String.fromCharCode(65 + b)}`));
      assert(text.includes(`${String.fromCharCode(65 + fa)} and ${String.fromCharCode(65 + fb)}`));
      failures++;
    }
    demonstrations++;
  }
  entry.operations.forEach((operation, index) => {
    const html = app.operationHtml(operation, index);
    operation.forEach((output, input) => assert(html.includes(`${String.fromCharCode(65 + input)} <b aria-label="becomes">→</b> ${String.fromCharCode(65 + output)}`)));
  });
  for (let selected = 0; selected < entry.partitions.length; selected++) {
    const svg = app.latticeSvg(entry, selected);
    assert.equal((svg.match(/data-partition=/g) || []).length, entry.partitions.length);
    assert.equal((svg.match(/class="lattice-node selected"/g) || []).length, 1);
    assert(svg.includes(`class="lattice-node selected" data-partition="${selected}"`));
    entry.partitions.forEach((p, i) => {
      assert(svg.includes(`Grouping ${i + 1}: ${app.escapeHtml(label(p))}`));
      assert(svg.includes(`G${i + 1}: ${app.escapeHtml(label(p))}`), 'Accessible SVG description names each grouping.');
    });
    assert.equal((svg.match(/<line /g) || []).length, entry.covers.length);
    for (const [lower, upper] of entry.covers) {
      assert(entry.order[lower][upper] && lower !== upper);
      assert(!entry.partitions.some((_, between) => between !== lower && between !== upper && entry.order[lower][between] && entry.order[between][upper]));
      assert(svg.includes(`data-lower="${lower}" data-upper="${upper}"`));
      assert(svg.includes(`G${lower + 1} to G${upper + 1}`), 'Accessible SVG description names each upward connection.');
    }
    assert(!/NaN|Infinity/.test(svg));
    const nodePositions = [...svg.matchAll(/data-partition="(\d+)" transform="translate\(([^,]+),([^\)]+)\)"/g)].map(match => ({ index: Number(match[1]), x: Number(match[2]), y: Number(match[3]) }));
    for (const a of nodePositions) for (const b of nodePositions) {
      if (a.index < b.index && a.y === b.y) assert(Math.abs(a.x - b.x) >= 119.999, `${entry.id}: diagram nodes need readable separation.`);
    }
    renderedNodes += entry.partitions.length;
    renderedEdges += entry.covers.length;
  }
  const exported = app.certificate(data, entry);
  assert.deepEqual(exported.entry, entry);
  assert.deepEqual(exported.source_sha256, data.source_sha256);
  assert.equal(exported.generator_sha256, data.generator_sha256);
  assert.equal(exported.minimum_scope, data.minimum_scope);
  const claims = app.claimsForEntry(registry, entry);
  const reviewedEntry = sourceDocuments.get('evidence/atlas-review.json').entries.find(item => item.id === entry.id);
  const expectedShapeKey = `poset-v1:${reviewedEntry.poset_canonical_sha256}`;
  const direct = claims.filter(claim => claim.entry_id === entry.id);
  assert.deepEqual(direct.map(claim => claim.id).sort(), [`construction:${entry.id}`, `minimum:${entry.id}`].sort(), 'Every entry needs its exact construction and minimum claims.');
  const renderedClaims = app.claimsHtml(registry, entry);
  for (const claim of claims) {
    assert.equal(claim.carrier_size, entry.carrier_size);
    assert.equal(claim.abstract_type, entry.abstract_type);
    assert.equal(claim.shape_key, expectedShapeKey);
    assert(renderedClaims.includes(app.escapeHtml(claim.id)));
    assert(renderedClaims.includes(app.escapeHtml(claim.statement)));
    assert(renderedClaims.includes(app.escapeHtml(claim.scope)));
    for (const sentence of [...claim.assumptions, ...claim.limits]) assert(renderedClaims.includes(app.escapeHtml(sentence)));
    for (const citation of claim.citations) {
      assert.equal(citation.sha256, sourceHashes.get(citation.path));
      assert.notEqual(resolvePointer(sourceDocuments.get(citation.path), citation.json_pointer), undefined, 'Each claim citation must resolve.');
    }
    if (claim.entry_id) {
      const entryIndex = data.entries.findIndex(item => item.id === entry.id);
      for (const field of ['id', 'partitions', 'operations', 'minimum_unary_operations']) {
        const citation = claim.citations.find(item => item.path === 'evidence/atlas.json' && item.json_pointer === `/entries/${entryIndex}/${field}`);
        assert(citation, `${claim.id}: missing source pointer for ${field}`);
        assert.deepEqual(resolvePointer(data, citation.json_pointer), entry[field]);
      }
      if (claim.kind === 'fixed_family_minimum') assert.equal(claim.minimum_unary_operations, entry.minimum_unary_operations);
    } else {
      assert(claim.entry_ids.includes(entry.id));
      const peers = data.entries.filter(item => item.carrier_size === entry.carrier_size && item.abstract_type === entry.abstract_type);
      assert.deepEqual([...claim.entry_ids].sort(), peers.map(item => item.id).sort());
      assert.deepEqual(claim.minimum_rule_counts, [...new Set(peers.map(item => item.minimum_unary_operations))].sort((a, b) => a - b));
    }
    entryClaimLinks++;
  }
  const exportWithClaims = app.certificate(data, entry, registry);
  assert.deepEqual(exportWithClaims.claims.ids, claims.map(claim => claim.id));
  assert.deepEqual(exportWithClaims.claims.sources, registry.sources);
  assert.equal(exportWithClaims.claims.namespace, registry.namespace);
}
assert.deepEqual(app.claimsForEntry(registry, { id: 'missing-entry' }), []);
assert.deepEqual(app.claimsForEntry(null, data.entries[0]), []);
assert(app.claimsHtml(null, data.entries[0]).includes('unavailable'));
assert.deepEqual(app.LESSON.operations, [[0, 1, 1]]);
const lessonPassing = allPartitions(3).filter(p => app.LESSON.operations.every(op => preserves(p, op))).map(label).sort();
assert.deepEqual(lessonPassing, ['A | B | C', 'A | BC', 'AB | C', 'ABC'].sort());
assert(app.checkGrouping(app.LESSON.pass, app.LESSON.operations).valid);
assert(!app.checkGrouping(app.LESSON.fail, app.LESSON.operations).valid);
assert.deepEqual(app.LESSON.partitions.map(label).sort(), lessonPassing);
const lessonSvg = app.latticeSvg(app.LESSON, 2, true);
const lessonNodePositions = [...lessonSvg.matchAll(/data-partition="(\d+)" transform="translate\(([^,]+),([^\)]+)\)"/g)].map(match => ({ index: Number(match[1]), x: Number(match[2]), y: Number(match[3]) }));
for (const a of lessonNodePositions) for (const b of lessonNodePositions) {
  if (a.index < b.index && a.y === b.y) assert(Math.abs(a.x - b.x) >= 120, 'Compact diagram nodes need readable separation.');
}
assert(!lessonSvg.includes('listed in the selection buttons'));
// Prove the friendly introduction is a relabeling of the actual saved B2 map.
const original = [0, 0, 2], friendlyToStored = [2, 0, 1];
assert.deepEqual(friendlyToStored.map(old => friendlyToStored.indexOf(original[old])), app.LESSON.operations[0]);
assert.equal(data.entries.length, 39);
assert.equal(data.abstract_types.length, 22);
assert.equal(app.filterEntries(data.entries, '4', 'all').length, 33);
const c4 = data.entries.filter(e => e.name === 'C4' && e.carrier_size === 4);
assert.deepEqual(c4.map(e => e.minimum_unary_operations).sort(), [1, 2]);
assert.equal(new Set(c4.map(e => e.abstract_type)).size, 1);
assert.equal(app.filterEntries(data.entries, '1', c4[0].abstract_type).length, 0);
assert.equal(app.escapeHtml('<script>"&\''), '&lt;script&gt;&quot;&amp;&#39;');
const html = fs.readFileSync(path.join(root, 'space/atlas.html'), 'utf8');
const ids = [...html.matchAll(/\bid="([^"]+)"/g)].map(match => match[1]);
assert.equal(ids.length, new Set(ids).size, 'HTML ids must be unique.');
const js = fs.readFileSync(path.join(root, 'space/atlas.js'), 'utf8');
for (const [, id] of js.matchAll(/byId\('([^']+)'\)/g)) assert(ids.includes(id), `Missing HTML element ${id}`);
assert(html.includes('<noscript>'));
assert(html.includes('src="atlas-claims.js"'));
assert(html.includes('docs/ATLAS_QUERY.md'));
assert(/id="entry-diagram"[^>]*tabindex="0"[^>]*aria-label=/.test(html), 'Wide diagrams must be keyboard accessible.');
assert(!/<script[^>]+src="https?:/.test(html), 'The atlas must load without remote JavaScript.');
console.log(`Atlas UI checks passed: ${data.entries.length} entries, ${demonstrations} grouping demonstrations, ${failures} rejection witnesses, ${renderedNodes} rendered nodes and ${renderedEdges} rendered edges across selection states, ${entryClaimLinks} claim links with checked source pointers.`);
