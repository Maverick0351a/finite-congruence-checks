/* A visual projection of atlas records. Layout is never mathematical evidence. */
(function () {
  'use strict';
  const quantity = (n, word) => `${n} ${word}${n === 1 ? '' : 's'}`;
  function buildGraph(atlas, registry, carrier = 'all', shape = 'all') {
    if (!atlas || atlas.schema_version !== 1 || !registry || registry.schema_version !== 1) {
      throw new Error('Atlas and claim records with schema version 1 are required.');
    }
    if (!['all', '1', '2', '3', '4'].includes(String(carrier))) throw new Error('Unknown object count.');
    if (shape !== 'all' && !atlas.abstract_types.some(item => item.id === shape)) throw new Error('Unknown shape.');
    const claims = new Map(registry.claims.map(claim => [claim.id, claim]));
    if (claims.size !== registry.claims.length) throw new Error('Duplicate claim IDs.');
    const entries = atlas.entries.filter(entry => (carrier === 'all' || entry.carrier_size === Number(carrier)) && (shape === 'all' || entry.abstract_type === shape));
    const shapes = new Map(), elements = [];
    for (const entry of entries) {
      const construction = claims.get(`construction:${entry.id}`), minimum = claims.get(`minimum:${entry.id}`);
      for (const claim of [construction, minimum]) {
        if (!claim || claim.entry_id !== entry.id || claim.carrier_size !== entry.carrier_size || claim.abstract_type !== entry.abstract_type || !/^poset-v1:[0-9a-f]{64}$/.test(claim.shape_key)) {
          throw new Error(`Claim identity mismatch for ${entry.id}.`);
        }
      }
      if (minimum.minimum_unary_operations !== entry.minimum_unary_operations || minimum.shape_key !== construction.shape_key) throw new Error(`Claim value mismatch for ${entry.id}.`);
      const shapeKey = construction.shape_key;
      if (!shapes.has(shapeKey)) shapes.set(shapeKey, { id: shapeKey, name: entry.name, abstract_type: entry.abstract_type, entries: [] });
      const group = shapes.get(shapeKey);
      if (group.abstract_type !== entry.abstract_type || [...shapes.values()].some(other => other.id !== shapeKey && other.abstract_type === entry.abstract_type)) throw new Error('Inconsistent shape identities.');
      group.entries.push(entry);
      elements.push({ data: { id: entry.id, kind: 'construction', label: `${entry.id}\n${quantity(entry.carrier_size, 'object')} · ${quantity(entry.minimum_unary_operations, 'rule')}`, entry_id: entry.id, shape_key: shapeKey, claim_ids: [construction.id, minimum.id] } });
      elements.push({ data: { id: `has-shape:${entry.id}`, source: entry.id, target: shapeKey, kind: 'has_shape', claim_ids: [construction.id] } });
    }
    const columns = Math.min(3, shapes.size);
    [...shapes.values()].forEach((group, index) => {
      const x = (index % columns) * 660, y = Math.floor(index / columns) * 400;
      elements.push({ data: { id: group.id, kind: 'shape', label: `${group.name}\nSHAPE`, abstract_type: group.abstract_type }, position: { x, y } });
      group.entries.forEach((entry, j) => {
        const rowSize = Math.min(3, group.entries.length - Math.floor(j / 3) * 3);
        elements.find(item => item.data.id === entry.id).position = { x: x + ((j % 3) - (rowSize - 1) / 2) * 195, y: y + 145 + Math.floor(j / 3) * 105 };
      });
    });
    return { entries, shapes: [...shapes.values()], elements };
  }

  function mount(atlas, registry, openEntry) {
    const get = id => document.getElementById(id);
    const shapeSelect = get('map-shape'), carrierSelect = get('map-carrier'), entrySelect = get('map-entry');
    let graph, cy = null, current = null;
    const esc = text => String(text).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
    const controls = ['map-zoom-in', 'map-zoom-out', 'map-fit', 'map-reset'];
    shapeSelect.innerHTML = '<option value="all">All shapes · overview</option>' + atlas.abstract_types.map(shape => `<option value="${esc(shape.id)}">${esc(shape.name)} · ${shape.lattice_elements} groupings</option>`).join('');
    shapeSelect.value = atlas.abstract_types.find(shape => shape.name === 'C4')?.id || 'all';
    function styles() {
      const css = getComputedStyle(document.documentElement), token = name => css.getPropertyValue(name).trim();
      return [
        { selector: 'node', style: { label: 'data(label)', color: '#ffffff', 'font-size': 13, 'font-family': 'system-ui, sans-serif', 'font-weight': 600, 'text-wrap': 'wrap', 'text-valign': 'center', 'text-halign': 'center', 'text-max-width': 155, 'border-width': 2, 'border-color': token('--graph-construction'), 'overlay-opacity': 0 } },
        { selector: 'node[kind = "construction"]', style: { shape: 'round-rectangle', width: 166, height: 62, 'background-color': token('--graph-construction') } },
        { selector: 'node[kind = "shape"]', style: { shape: 'diamond', width: 136, height: 104, 'background-color': token('--graph-shape'), 'border-color': token('--graph-shape') } },
        { selector: 'edge', style: { width: 2, 'line-color': token('--graph-edge'), 'curve-style': 'bezier', 'target-arrow-shape': 'none' } },
        { selector: 'node.inspected', style: { 'border-width': 5, 'border-color': token('--graph-selected'), 'underlay-color': token('--graph-selected'), 'underlay-opacity': 0.15, 'underlay-padding': 7 } },
      ];
    }
    function fit() {
      if (!cy || !cy.nodes().length) return;
      cy.resize(); cy.fit(undefined, 35);
      if (cy.zoom() > 1.3) { cy.zoom(1.3); cy.center(); }
    }
    function select(id) {
      current = graph.entries.find(entry => entry.id === id) || null;
      entrySelect.value = current ? current.id : '';
      get('map-open-entry').disabled = !current;
      if (cy) { cy.nodes().removeClass('inspected'); if (current) cy.getElementById(current.id).addClass('inspected'); }
      if (!current) { get('map-selection').innerHTML = '<p>No constructions match both filters. Choose another shape or object count.</p>'; return; }
      const node = graph.elements.find(item => item.data.id === current.id).data;
      const claims = node.claim_ids.map(id => registry.claims.find(claim => claim.id === id));
      get('map-selection').innerHTML = `<p class="map-entry-id">${esc(current.id)}</p><p><strong>${esc(current.name)}</strong> shape · ${current.carrier_size} objects<br><strong>${current.minimum_unary_operations} minimum unary rule${current.minimum_unary_operations === 1 ? '' : 's'}</strong> for this exact grouping family.</p><p class="map-evidence">✓ Computationally checked</p><details><summary>Claim IDs &amp; source records</summary>${claims.map(claim => `<p><code>${esc(claim.id)}</code></p>`).join('')}<p class="small">Stable shape key</p><code>${esc(node.shape_key)}</code><p class="small">${esc(claims[1].limits[0])}</p><a href="atlas-claims.json" download>Download claims and citations ↓</a></details>`;
    }
    function render() {
      try { graph = buildGraph(atlas, registry, carrierSelect.value, shapeSelect.value); }
      catch (error) {
        if (cy) { cy.destroy(); cy = null; }
        controls.forEach(id => { get(id).disabled = true; });
        entrySelect.replaceChildren(); entrySelect.disabled = true;
        current = null; get('map-open-entry').disabled = true;
        get('map-selection').textContent = 'Map records could not be linked to their claims.';
        get('map-summary').textContent = error.message;
        return;
      }
      const previous = current?.id;
      entrySelect.innerHTML = graph.entries.map(entry => `<option value="${esc(entry.id)}">${esc(entry.id)} · ${quantity(entry.carrier_size, 'object')} · ${quantity(entry.minimum_unary_operations, 'rule')}</option>`).join('');
      entrySelect.disabled = !graph.entries.length;
      get('map-summary').textContent = `${quantity(graph.entries.length, 'construction')} · ${quantity(graph.shapes.length, 'shape')}. ${carrierSelect.value === 'all' ? 'Object counts can differ here; compare the labels before comparing rule counts.' : `Every construction here uses ${quantity(Number(carrierSelect.value), 'object')}.`}${shapeSelect.value === 'all' ? ' Choose one shape for a closer view.' : ''}`;
      if (cy) { cy.destroy(); cy = null; }
      if (typeof window.cytoscape === 'function') {
        try {
          cy = window.cytoscape({ container: get('construction-map'), elements: graph.elements, style: styles(), layout: { name: 'preset', fit: false }, minZoom: 0.08, maxZoom: 3, userZoomingEnabled: false, boxSelectionEnabled: false, autounselectify: true });
          cy.on('tap', 'node[kind = "construction"]', event => select(event.target.id()));
          cy.on('tap', 'node[kind = "shape"]', event => { shapeSelect.value = event.target.data('abstract_type'); render(); });
          fit();
        } catch (_) { if (cy) cy.destroy(); cy = null; }
      }
      get('map-fallback').hidden = Boolean(cy);
      get('construction-map').hidden = !cy;
      controls.forEach(id => { get(id).disabled = !cy || !graph.entries.length; });
      select(graph.entries.some(entry => entry.id === previous) ? previous : graph.entries[0]?.id);
    }
    shapeSelect.addEventListener('change', render);
    carrierSelect.addEventListener('change', render);
    entrySelect.addEventListener('change', () => select(entrySelect.value));
    get('map-open-entry').addEventListener('click', () => { if (current) openEntry(current); });
    get('map-fit').addEventListener('click', fit);
    get('map-reset').addEventListener('click', render);
    for (const [id, factor] of [['map-zoom-in', 1.25], ['map-zoom-out', 0.8]]) {
      get(id).addEventListener('click', () => { if (cy) cy.zoom({ level: cy.zoom() * factor, renderedPosition: { x: cy.width() / 2, y: cy.height() / 2 } }); });
    }
    if (typeof ResizeObserver !== 'undefined') new ResizeObserver(fit).observe(get('construction-map'));
    else window.addEventListener('resize', fit);
    window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => { if (cy) cy.style(styles()); });
    render();
  }
  if (typeof module !== 'undefined' && module.exports) module.exports = { buildGraph };
  if (typeof window !== 'undefined') window.AtlasMap = { buildGraph, mount };
}());
