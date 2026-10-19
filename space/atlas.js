/* The display is a view of recorded data. Grouping demonstrations run locally. */
(function () {
  'use strict';
  const LETTERS = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
  const GITHUB = 'https://github.com/Maverick0351a/finite-congruence-checks';
  const LESSON = Object.freeze({
    operations: [[0, 1, 1]],
    partitions: [[0, 1, 2], [0, 0, 1], [0, 1, 1], [0, 0, 0]],
    pass: [0, 1, 1], fail: [0, 1, 0],
    covers: [[0, 1], [0, 2], [1, 3], [2, 3]],
  });
  function escapeHtml(value) {
    return String(value).replace(/[&<>"']/g, x => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[x]);
  }
  function blocks(partition) {
    const result = new Map();
    partition.forEach((group, object) => {
      if (!result.has(group)) result.set(group, []);
      result.get(group).push(object);
    });
    return [...result.values()];
  }
  function partitionLabel(partition) {
    return blocks(partition).map(group => group.map(i => LETTERS[i]).join('')).join(' | ');
  }
  function partitions(n) {
    const result = [];
    function visit(prefix, largest) {
      if (prefix.length === n) { result.push(prefix); return; }
      for (let group = 0; group <= largest + 1; group++) visit([...prefix, group], Math.max(largest, group));
    }
    visit([0], 0);
    return result;
  }
  function checkGrouping(partition, operations) {
    for (let k = 0; k < operations.length; k++) {
      const op = operations[k];
      for (let a = 0; a < partition.length; a++) {
        for (let b = a + 1; b < partition.length; b++) {
          if (partition[a] === partition[b] && partition[op[a]] !== partition[op[b]]) {
            return { valid: false, witness: { operation: k, inputs: [a, b], outputs: [op[a], op[b]] } };
          }
        }
      }
    }
    return { valid: true, witness: null };
  }
  function operationHtml(operation, index) {
    return `<div class="operation"><strong>Rule ${index + 1}</strong><div class="mapping-row">${operation.map((output, input) => `<span>${LETTERS[input]} <b aria-label="becomes">→</b> ${LETTERS[output]}</span>`).join('')}</div></div>`;
  }
  function blockHtml(partition) {
    return `<div class="blocks" aria-label="Groups: ${escapeHtml(partitionLabel(partition))}">${blocks(partition).map(group => `<span class="block">${group.map(i => LETTERS[i]).join(' ')}</span>`).join('')}</div>`;
  }
  function groupingHtml(partition, operations) {
    const result = checkGrouping(partition, operations);
    if (!result.valid) {
      const { operation, inputs, outputs } = result.witness;
      return `<strong>This grouping fails.</strong>${blockHtml(partition)}<p><strong>${LETTERS[inputs[0]]} and ${LETTERS[inputs[1]]}</strong> begin in the same group. Rule ${operation + 1} sends them to <strong>${LETTERS[outputs[0]]} and ${LETTERS[outputs[1]]}</strong>, which are in different groups.</p><p>Choosing a different member of one group changes the output group.</p>`;
    }
    if (!operations.length) return `<strong>This grouping works.</strong>${blockHtml(partition)}<p>There are no rules to violate, so every possible grouping is allowed.</p>`;
    const nonSingleton = blocks(partition).filter(group => group.length > 1);
    if (!nonSingleton.length) return `<strong>This grouping works.</strong>${blockHtml(partition)}<p>Every group contains one object. There are no different objects in a group whose outputs could split apart.</p>`;
    const examples = operations.map((op, index) => {
      const group = nonSingleton[0], outputs = group.map(i => op[i]);
      return `<p><strong>Rule ${index + 1}:</strong> ${group.map(i => LETTERS[i]).join(', ')} become ${outputs.map(i => LETTERS[i]).join(', ')}. Those outputs are in the same group.</p>`;
    }).join('');
    return `<strong>This grouping works.</strong>${blockHtml(partition)}${examples}<p>Every group passes this test for every rule. Repeated letters above record outputs, not extra objects.</p>`;
  }
  function latticeSvg(entry, selected = -1, compact = false) {
    const count = entry.partitions.length;
    const heights = Array(count).fill(-1);
    function height(i, visiting = new Set()) {
      if (heights[i] >= 0) return heights[i];
      if (visiting.has(i)) throw new Error('The saved order diagram contains a cycle.');
      const next = new Set(visiting).add(i);
      const lower = entry.covers.filter(([, upper]) => upper === i).map(([lo]) => lo);
      return heights[i] = lower.length ? 1 + Math.max(...lower.map(lo => height(lo, next))) : 0;
    }
    for (let i = 0; i < count; i++) height(i);
    const maximum = Math.max(...heights), rows = Array.from({ length: maximum + 1 }, () => []);
    heights.forEach((rank, i) => rows[rank].push(i));
    const widest = Math.max(...rows.map(row => row.length));
    const width = compact && widest === 1 ? 180 : Math.max(compact ? 180 : 400, (widest + 1) * 120);
    const rowGap = compact ? 67 : 83, top = 34;
    const svgHeight = maximum * rowGap + 76;
    const positions = Array(count);
    rows.forEach((row, rank) => row.forEach((i, column) => {
      positions[i] = { x: width * (column + 1) / (row.length + 1), y: top + (maximum - rank) * rowGap };
    }));
    const lines = entry.covers.map(([lower, upper]) => `<line class="lattice-edge" data-lower="${lower}" data-upper="${upper}" x1="${positions[lower].x}" y1="${positions[lower].y}" x2="${positions[upper].x}" y2="${positions[upper].y}"/>`).join('');
    const nodes = positions.map(({ x, y }, i) => `<g class="lattice-node${i === selected ? ' selected' : ''}" data-partition="${i}" transform="translate(${x},${y})"><title>Grouping ${i + 1}: ${escapeHtml(partitionLabel(entry.partitions[i]))}${i === selected ? ', selected' : ''}</title><rect x="-53" y="-22" width="106" height="44" rx="7"/><text class="node-index" text-anchor="middle" y="-6">G${i + 1}</text><text text-anchor="middle" y="12">${escapeHtml(partitionLabel(entry.partitions[i]))}</text></g>`).join('');
    const groupingDescription = entry.partitions.map((partition, i) => `G${i + 1}: ${partitionLabel(partition)}${i === selected ? ' (selected)' : ''}`).join('; ');
    const edgeDescription = entry.covers.length ? `Upward connections: ${entry.covers.map(([lower, upper]) => `G${lower + 1} to G${upper + 1}`).join('; ')}.` : 'There are no connections because the diagram has only one grouping.';
    const description = `Order diagram with ${count} valid grouping${count === 1 ? '' : 's'}. A bar separates groups. Moving upward merges groups. ${groupingDescription}. ${edgeDescription}`;
    return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${svgHeight}"${compact ? '' : ` style="min-width:${width}px"`} role="img" aria-label="${escapeHtml(description)}">${lines}${nodes}</svg>`;
  }
  function filterEntries(entries, carrier, shape) {
    return entries.filter(entry => (carrier === 'all' || entry.carrier_size === Number(carrier)) && (shape === 'all' || entry.abstract_type === shape));
  }
  function claimsForEntry(registry, entry) {
    if (!registry || registry.schema_version !== 1 || !Array.isArray(registry.claims)) return [];
    return registry.claims.filter(claim => claim.entry_id === entry.id || (Array.isArray(claim.entry_ids) && claim.entry_ids.includes(entry.id)));
  }
  function claimsHtml(registry, entry) {
    const claims = claimsForEntry(registry, entry);
    if (!claims.length) return '<p>The offline claim registry is unavailable for this entry. The mathematical data remains available below.</p>';
    const unique = field => [...new Set(claims.flatMap(claim => claim[field] || []))];
    const list = items => `<ul>${items.map(item => `<li>${escapeHtml(item)}</li>`).join('')}</ul>`;
    const records = claims.map(claim => `<div class="claim-record"><code>${escapeHtml(claim.id)}</code><p>${escapeHtml(claim.statement)}</p></div>`).join('');
    const scopes = [...new Set(claims.map(claim => claim.scope))];
    const evidence = [...new Set(claims.map(claim => claim.evidence_status.replace(/_/g, ' ')))];
    return `<h4>Claims attached to this entry</h4><p>These stable IDs connect the displayed result to source locations and file hashes in the downloadable registry.</p>${records}<details><summary>Read the assumptions, limits, and evidence status</summary><p><strong>Evidence:</strong> ${escapeHtml(evidence.join('; '))}.</p><p><strong>Scope:</strong> ${scopes.map(escapeHtml).join(' ')}</p><p><strong>Assumptions</strong></p>${list(unique('assumptions'))}<p><strong>Limits</strong></p>${list(unique('limits'))}</details><p><a href="atlas-claims.json" download>Download all claim records and source citations ↓</a> · <a href="${GITHUB}/blob/main/docs/ATLAS_QUERY.md">Query guide ↗</a></p>`;
  }
  function certificate(data, entry, registry = null) {
    const record = { schema_version: data.schema_version, scope: data.scope, evidence_status: data.evidence_status, minimum_scope: data.minimum_scope, source_sha256: data.source_sha256, generator_sha256: data.generator_sha256, hash_encoding: data.hash_encoding, entry };
    const claims = claimsForEntry(registry, entry);
    if (claims.length) record.claims = { registry: 'atlas-claims.json', namespace: registry.namespace, ids: claims.map(claim => claim.id), sources: registry.sources };
    return record;
  }
  const api = { LESSON, escapeHtml, blocks, partitionLabel, partitions, checkGrouping, operationHtml, groupingHtml, latticeSvg, filterEntries, claimsForEntry, claimsHtml, certificate };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  if (typeof document === 'undefined') return;

  const byId = id => document.getElementById(id);
  const data = window.ATLAS_DATA;
  const registry = window.ATLAS_CLAIMS;
  function renderLesson(which) {
    const selected = LESSON[which], result = byId('lesson-result');
    result.innerHTML = groupingHtml(selected, LESSON.operations);
    result.classList.toggle('is-fail', !checkGrouping(selected, LESSON.operations).valid);
    document.querySelectorAll('[data-lesson]').forEach(button => button.setAttribute('aria-pressed', String(button.dataset.lesson === which)));
    const selectedIndex = LESSON.partitions.findIndex(p => p.join(',') === selected.join(','));
    byId('lesson-diagram').innerHTML = latticeSvg(LESSON, selectedIndex, true);
  }
  document.querySelectorAll('[data-lesson]').forEach(button => button.addEventListener('click', () => renderLesson(button.dataset.lesson)));
  renderLesson('pass');
  if (!data || data.schema_version !== 1 || !Array.isArray(data.entries) || !data.entries.length) {
    byId('atlas-loading').textContent = 'The atlas data could not be loaded. Keep atlas-data.js next to this page, or open the repository’s saved evidence.';
    byId('comparison').hidden = true;
    return;
  }
  let selectedEntry = data.entries.find(entry => entry.name === 'B2' && entry.carrier_size === 3) || data.entries[0];
  let selectedGrouping = 0;
  let lastDownloadUrl = null;
  function renderGrouping(index) {
    selectedGrouping = index;
    const partition = selectedEntry.partitions[index];
    byId('entry-grouping').innerHTML = groupingHtml(partition, selectedEntry.operations);
    byId('entry-diagram').innerHTML = latticeSvg(selectedEntry, index);
    byId('grouping-list').querySelectorAll('button').forEach(button => button.setAttribute('aria-pressed', String(Number(button.dataset.grouping) === index)));
  }
  function renderEntry(entry) {
    selectedEntry = entry;
    const n = entry.carrier_size, minimum = entry.minimum_unary_operations;
    const shape = entry.name.startsWith('Shape ') ? `${entry.name} · ${entry.partitions.length} grouping${entry.partitions.length === 1 ? '' : 's'}` : `${entry.name} · ${n} object${n === 1 ? '' : 's'}`;
    byId('entry-kicker').textContent = `ENTRY ${entry.id} / SHAPE ${entry.abstract_type}`;
    byId('entry-title').textContent = shape;
    byId('entry-intro').textContent = `${n} object${n === 1 ? '' : 's'} and ${minimum} rule${minimum === 1 ? '' : 's'} give exactly ${entry.partitions.length} valid grouping${entry.partitions.length === 1 ? '' : 's'}. Each entry has its own rules and object labels; check the arrows again.`;
    byId('entry-facts').innerHTML = `<div><strong>${n}</strong><span>object${n === 1 ? '' : 's'}</span></div><div><strong>${minimum}</strong><span>minimum unary rule${minimum === 1 ? '' : 's'}</span></div><div><strong>${entry.partitions.length}</strong><span>valid grouping${entry.partitions.length === 1 ? '' : 's'}</span></div>`;
    byId('entry-objects').innerHTML = Array.from({ length: n }, (_, i) => `<span class="object">${LETTERS[i]}</span>`).join('');
    byId('entry-operations').innerHTML = entry.operations.length ? entry.operations.map(operationHtml).join('') : '<p class="small">This system has no rules. Every partition of its objects is therefore a valid grouping. Allowing zero operations is part of this atlas’s stated convention.</p>';
    byId('grouping-list').innerHTML = entry.partitions.map((partition, index) => `<button type="button" data-grouping="${index}" aria-pressed="false"><span>GROUPING ${index + 1}</span>${escapeHtml(partitionLabel(partition))}</button>`).join('');
    byId('grouping-list').querySelectorAll('button').forEach(button => button.addEventListener('click', () => renderGrouping(Number(button.dataset.grouping))));
    const rejected = partitions(n).find(partition => !checkGrouping(partition, entry.operations).valid);
    byId('entry-failure').innerHTML = rejected ? `<div class="grouping-result is-fail">${groupingHtml(rejected, entry.operations)}</div>` : '<p>Every possible grouping works for this entry. There is no failing grouping to display.</p>';
    byId('failure-details').open = false;
    byId('entry-takeaway').textContent = minimum === 0 ? `Takeaway: the objects alone already give this shape. Adding a rule is unnecessary for this grouping family.` : `Takeaway: ${minimum === 1 ? 'this one rule allows' : `these ${minimum} rules allow`} every displayed grouping and ${minimum === 1 ? 'excludes' : 'exclude'} every other partition. Exhaustive checking shows that fewer unary rules cannot produce this exact family on these ${n} objects.`;
    byId('entry-provenance').innerHTML = `<dl><dt>Entry</dt><dd>${escapeHtml(entry.id)}</dd><dt>Abstract shape</dt><dd>${escapeHtml(entry.abstract_type)}</dd><dt>Labeled families represented</dt><dd>${entry.orbit_size} under object renaming</dd><dt>Stored object indices</dt><dd>${Array.from({ length: n }, (_, i) => `${LETTERS[i]} = ${i}`).join(', ')}</dd><dt>Evidence type</dt><dd>Exhaustive finite computation and independent verification</dd></dl><p><a href="${GITHUB}/blob/main/evidence/atlas-review.json">Inspect the independent verification record ↗</a></p>`;
    byId('entry-claims').innerHTML = claimsHtml(registry, entry);
    byId('entry-context').hidden = entry.id !== 'n4-E16709';
    byId('entry-json').textContent = JSON.stringify(certificate(data, entry, registry), null, 2);
    byId('entry-list').querySelectorAll('button').forEach(button => button.setAttribute('aria-pressed', String(button.dataset.entry === entry.id)));
    const firstNontrivial = entry.partitions.findIndex(partition => blocks(partition).some(group => group.length > 1) && blocks(partition).length > 1);
    renderGrouping(firstNontrivial >= 0 ? firstNontrivial : 0);
  }
  function renderCatalog() {
    const visible = filterEntries(data.entries, byId('carrier-filter').value, byId('shape-filter').value);
    byId('entry-count').textContent = `${visible.length} ${visible.length === 1 ? 'entry' : 'entries'} shown`;
    byId('entry-list').innerHTML = visible.length ? visible.map(entry => `<button type="button" data-entry="${escapeHtml(entry.id)}" aria-pressed="${entry.id === selectedEntry.id}"><strong>${escapeHtml(entry.name)} · ${entry.carrier_size} object${entry.carrier_size === 1 ? '' : 's'}</strong><span>${entry.partitions.length} grouping${entry.partitions.length === 1 ? '' : 's'} · ${entry.minimum_unary_operations} rule${entry.minimum_unary_operations === 1 ? '' : 's'}</span><span>${escapeHtml(entry.id)}</span></button>`).join('') : '<p class="small">No entries match both filters. Try a different object count or shape.</p>';
    byId('entry-list').querySelectorAll('button').forEach(button => button.addEventListener('click', () => renderEntry(data.entries.find(entry => entry.id === button.dataset.entry))));
    if (visible.length && !visible.some(entry => entry.id === selectedEntry.id)) renderEntry(visible[0]);
    byId('entry-title').closest('.entry-detail').hidden = !visible.length;
  }
  byId('carrier-filter').addEventListener('change', renderCatalog);
  byId('shape-filter').addEventListener('change', renderCatalog);
  byId('shape-filter').insertAdjacentHTML('beforeend', data.abstract_types.map(shape => `<option value="${escapeHtml(shape.id)}">${escapeHtml(shape.name)} (${shape.lattice_elements} grouping${shape.lattice_elements === 1 ? '' : 's'})</option>`).join(''));
  const totalFamilies = data.carrier_summary.reduce((sum, row) => sum + row.labeled_relation_families, 0);
  byId('atlas-totals').innerHTML = `<div><strong>${totalFamilies}</strong><span>labeled grouping families</span></div><div><strong>${data.entries.length}</strong><span>entries after renaming</span></div><div><strong>${data.abstract_types.length}</strong><span>distinct abstract shapes</span></div>`;
  byId('count-table').innerHTML = `<table><caption class="small">Complete counts for each object count</caption><thead><tr><th scope="col">Objects</th><th scope="col">Labeled families</th><th scope="col">After renaming</th><th scope="col">Abstract shapes</th></tr></thead><tbody>${data.carrier_summary.map(row => `<tr><th scope="row">${row.carrier_size}</th><td>${row.labeled_relation_families}</td><td>${row.embedding_orbits}</td><td>${row.abstract_types}</td></tr>`).join('')}</tbody></table>`;
  const comparisons = [1, 2].map(minimum => data.entries.find(entry => entry.name === 'C4' && entry.carrier_size === 4 && entry.minimum_unary_operations === minimum)).filter(Boolean);
  byId('comparison-cards').innerHTML = comparisons.map(entry => `<article class="comparison-card"><p class="eyebrow">FOUR OBJECTS / FOUR GROUPINGS</p><h3>${entry.minimum_unary_operations === 1 ? 'One rule is enough.' : 'Two rules are necessary.'}</h3><p class="comparison-caption">Read the groups inside each node: they distinguish this construction.</p><div class="mini-chain">${latticeSvg(entry, -1, true)}</div>${entry.operations.map(operationHtml).join('')}<button class="button secondary" type="button" data-compare="${escapeHtml(entry.id)}">Explore this entry ↗</button></article>`).join('');
  byId('comparison-cards').querySelectorAll('button').forEach(button => button.addEventListener('click', () => {
    byId('carrier-filter').value = '4';
    byId('shape-filter').value = comparisons[0].abstract_type;
    renderCatalog();
    renderEntry(data.entries.find(entry => entry.id === button.dataset.compare));
    byId('entry-title').scrollIntoView({ behavior: window.matchMedia('(prefers-reduced-motion: reduce)').matches ? 'instant' : 'smooth', block: 'start' });
    byId('entry-title').setAttribute('tabindex', '-1');
    byId('entry-title').focus({ preventScroll: true });
  }));
  byId('download-entry').addEventListener('click', () => {
    if (lastDownloadUrl) URL.revokeObjectURL(lastDownloadUrl);
    lastDownloadUrl = URL.createObjectURL(new Blob([JSON.stringify(certificate(data, selectedEntry, registry), null, 2) + '\n'], { type: 'application/json' }));
    const link = document.createElement('a');
    link.href = lastDownloadUrl;
    link.download = `atlas-${selectedEntry.id}.json`;
    document.body.append(link); link.click(); link.remove();
  });
  byId('reproduce-commands').textContent = 'python scripts/build_atlas_data.py --check\npython scripts/check_atlas.py --check-receipt evidence/atlas-review.json\npython scripts/check_atlas.py --out runs/atlas-review.json\npython scripts/query_atlas.py build-claims --check\npython -m unittest discover -s scripts -p "test_atlas*.py" -v\nnode scripts/check_atlas_ui.cjs\nnode scripts/check_atlas_map.cjs';
  byId('copy-commands').addEventListener('click', async () => {
    try {
      await navigator.clipboard.writeText(byId('reproduce-commands').textContent);
      byId('copy-status').textContent = 'Commands copied.';
    } catch (_) {
      byId('copy-status').textContent = 'Copy is unavailable in this browser context. Select the commands above and copy them with your keyboard.';
    }
  });
  byId('source-record').textContent = JSON.stringify({ scope: data.scope, evidence_status: data.evidence_status, minimum_scope: data.minimum_scope, hash_encoding: data.hash_encoding, generator_sha256: data.generator_sha256, source_sha256: data.source_sha256 }, null, 2);
  byId('atlas-loading').hidden = true;
  byId('atlas-app').hidden = false;
  renderCatalog();
  const requestedEntry = data.entries.find(entry => entry.id === new URLSearchParams(window.location.search).get('entry'));
  if (requestedEntry) selectedEntry = requestedEntry;
  renderEntry(selectedEntry);
  if (window.AtlasMap) window.AtlasMap.mount(data, registry, entry => {
    byId('carrier-filter').value = String(entry.carrier_size);
    byId('shape-filter').value = entry.abstract_type;
    renderCatalog();
    renderEntry(entry);
    const title = byId('entry-title');
    title.setAttribute('tabindex', '-1');
    title.scrollIntoView({ block: 'start', behavior: window.matchMedia('(prefers-reduced-motion: reduce)').matches ? 'instant' : 'smooth' });
    title.focus({ preventScroll: true });
  });
}());
