/* Validate the visual projection against independent evidence, using real Cytoscape. */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const root = path.resolve(__dirname, '..');
const read = file => fs.readFileSync(path.join(root, file), 'utf8');
const atlas = JSON.parse(read('space/atlas-data.json'));
const registry = JSON.parse(read('space/atlas-claims.json'));
const review = JSON.parse(read('evidence/atlas-review.json'));
const manifest = JSON.parse(read('space/vendor/manifest.json'));
for (const [name, expected] of Object.entries(manifest.sha256)) {
  assert.equal(crypto.createHash('sha256').update(fs.readFileSync(path.join(root, 'space/vendor', name))).digest('hex'), expected, 'Vendored file hash: ' + name);
}
const cytoscape = require('../space/vendor/cytoscape-3.34.4.min.js');
const { buildGraph } = require('../space/atlas-map.js');
assert.equal(cytoscape.version, manifest.version);
assert(read('space/atlas.html').includes(`src="vendor/cytoscape-${manifest.version}.min.js"`));
const fresh = () => JSON.parse(JSON.stringify(registry));
let filterChecks = 0, linkedEntries = 0;
for (const carrier of ['all', '1', '2', '3', '4']) {
  for (const shape of ['all', ...atlas.abstract_types.map(shape => shape.id)]) {
    const graph = buildGraph(atlas, registry, carrier, shape);
    const expectedEntries = atlas.entries.filter(entry => (carrier === 'all' || entry.carrier_size === Number(carrier)) && (shape === 'all' || entry.abstract_type === shape));
    const cy = cytoscape({ headless: true, elements: graph.elements, layout: { name: 'preset' } });
    assert.equal(cy.nodes('[kind="construction"]').length, expectedEntries.length);
    assert.equal(cy.edges().length, expectedEntries.length);
    const shapes = new Set();
    for (const entry of expectedEntries) {
      const independent = review.entries.find(record => record.id === entry.id);
      const key = 'poset-v1:' + independent.poset_canonical_sha256;
      shapes.add(key);
      const node = cy.getElementById(entry.id);
      assert.equal(node.data('shape_key'), key);
      assert.equal(node.connectedEdges().length, 1);
      const edge = node.connectedEdges()[0];
      assert.equal(edge.source().id(), entry.id);
      assert.equal(edge.target().id(), key);
      assert.equal(edge.data('kind'), 'has_shape');
      assert(node.data('label').includes(`${entry.minimum_unary_operations} rule${entry.minimum_unary_operations === 1 ? '' : 's'}`));
      for (const id of node.data('claim_ids')) {
        const claim = registry.claims.find(claim => claim.id === id);
        assert.equal(claim.entry_id, entry.id);
        assert.equal(claim.shape_key, key);
        assert.equal(claim.carrier_size, entry.carrier_size);
        assert(claim.citations.some(cite => cite.path === 'evidence/atlas-review.json'));
      }
      linkedEntries++;
    }
    assert.equal(cy.nodes('[kind="shape"]').length, shapes.size);
    assert.equal(cy.elements().components().length, shapes.size);
    for (const node of cy.nodes()) assert(Number.isFinite(node.position('x')) && Number.isFinite(node.position('y')));
    cy.destroy();
    filterChecks++;
  }
}
const c4 = buildGraph(atlas, registry, '4', atlas.abstract_types.find(shape => shape.name === 'C4').id);
assert.deepEqual(c4.entries.map(entry => entry.id).sort(), ['n4-E16403', 'n4-E16457']);
assert.deepEqual(c4.entries.map(entry => entry.minimum_unary_operations).sort(), [1, 2]);
assert.equal(buildGraph(atlas, registry).elements.length, 100); // 39 constructions, 22 shapes, 39 links.
assert.throws(() => buildGraph(atlas, registry, '5'), /Unknown object count/);
assert.throws(() => buildGraph(atlas, registry, 'all', 'missing'), /Unknown shape/);
assert.throws(() => buildGraph(atlas, null), /required/);
let bad = fresh(); bad.claims = bad.claims.filter(claim => claim.id !== 'construction:n4-E16457');
assert.throws(() => buildGraph(atlas, bad), /identity mismatch/);
bad = fresh(); bad.claims.find(claim => claim.id === 'minimum:n4-E16457').minimum_unary_operations = 1;
assert.throws(() => buildGraph(atlas, bad), /value mismatch/);
bad = fresh(); bad.claims.push(bad.claims[0]);
assert.throws(() => buildGraph(atlas, bad), /Duplicate/);
bad = fresh(); bad.claims.find(claim => claim.id === 'construction:n4-E16457').shape_key = 'T06';
assert.throws(() => buildGraph(atlas, bad), /identity mismatch/);

// Check the actual theme tokens, rather than an unrelated palette fixture.
const css = read('space/atlas.css');
const roots = [...css.matchAll(/:root\s*\{([^}]+)\}/g)].map(match => Object.fromEntries([...match[1].matchAll(/(--[\w-]+):\s*(#[\da-f]{6})(?=[;}\s])/gi)].map(m => [m[1], m[2]])));
const light = { ...roots[0], ...roots[1] }, dark = { ...light, ...roots[2] };
function luminance(hex) {
  const rgb = hex.slice(1).match(/../g).map(pair => parseInt(pair, 16) / 255).map(c => c <= 0.04045 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4);
  return 0.2126 * rgb[0] + 0.7152 * rgb[1] + 0.0722 * rgb[2];
}
function contrast(a, b) { const values = [luminance(a), luminance(b)].sort((x, y) => x - y); return (values[1] + 0.05) / (values[0] + 0.05); }
let lowest = 100;
for (const theme of [light, dark]) {
  for (const foreground of ['--ink', '--body', '--muted', '--teal', '--accent']) {
    for (const background of ['--paper', '--ground', '--surface-soft']) {
      const ratio = contrast(theme[foreground], theme[background]);
      assert(ratio >= 4.5, `${foreground} on ${background}: ${ratio.toFixed(2)}:1`);
      lowest = Math.min(lowest, ratio);
    }
  }
  for (const token of ['--graph-shape', '--graph-construction']) assert(contrast('#ffffff', theme[token]) >= 4.5);
  for (const token of ['--graph-edge', '--control-border', '--graph-selected']) assert(contrast(theme[token], theme['--ground']) >= 3);
}
console.log(`Atlas map verified: ${filterChecks} filter combinations, ${linkedEntries} entry links, all 22 shape components, C4 comparison, seven rejection controls, vendor hashes, light/dark text contrast >= ${lowest.toFixed(2)}:1.`);
