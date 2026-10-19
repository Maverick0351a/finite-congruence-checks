/* Reading guide for one exact construction. Mathematical proofs remain in Lean. */
(function () {
  'use strict';
  const esc = value => String(value).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  function label(p) {
    const groups = new Map();
    p.forEach((g, x) => { if (!groups.has(g)) groups.set(g, []); groups.get(g).push(x); });
    return [...groups.values()].map(g => `{${g.join(', ')}}`).join(' | ');
  }
  function check(p, ops) {
    for (let k = 0; k < ops.length; k++) for (let x = 0; x < 4; x++) for (let y = x + 1; y < 4; y++) {
      if (p[x] === p[y] && p[ops[k][x]] !== p[ops[k][y]]) return {operation:k, pair:[x,y], outputs:[ops[k][x], ops[k][y]]};
    }
    return null;
  }
  function groupingResult(p, ops) {
    const v = check(p, ops);
    if (v) return `<h4>This grouping fails</h4><p>${esc(label(p))} puts ${v.pair.join(' and ')} together.</p><p class="counterexample">${'fg'[v.operation]}(${v.pair[0]}) = ${v.outputs[0]} &nbsp; · &nbsp; ${'fg'[v.operation]}(${v.pair[1]}) = ${v.outputs[1]}</p><p>Those outputs are in different groups. This pair is a concrete witness to the failure.</p>`;
    return `<h4>This grouping works</h4><p>${esc(label(p))}</p><p>For every pair of inputs together, both f and g send the pair to outputs together. All pairs and both rules have been checked in this browser.</p>`;
  }
  function diagram(groups) {
    const positions = [[200,310],[82,222],[82,124],[318,174],[200,28]];
    const covers = [[0,1],[1,2],[2,4],[0,3],[3,4]];
    return `<svg viewBox="0 0 400 345" role="img" aria-label="N5: bottom below a below b below top, with c between bottom and top. Each node labels a complete grouping.">${covers.map(([a,b])=>`<line x1="${positions[a][0]}" y1="${positions[a][1]}" x2="${positions[b][0]}" y2="${positions[b][1]}"/>`).join('')}${groups.map((g,i)=>{const [x,y]=positions[i];return `<g><rect x="${x-76}" y="${y-23}" width="152" height="48" rx="8"/><text class="n5-label" x="${x}" y="${y-4}" text-anchor="middle">${['⊥','a','b','c','⊤'][i]}</text><text x="${x}" y="${y+15}" text-anchor="middle">${esc(label(g.partition).replace(/[{}, ]/g,''))}</text></g>`;}).join('')}</svg>`;
  }
  function graphElements(data) {
    const positions = {paper:[150,40], tables:[150,190], classification:[150,340], bridge:[150,490], criterion:[470,340], definitions:[470,190], target:[470,490]};
    const names = {paper:'Paper\nTheorem 2.2',tables:'Saved N5\nThese exact rules',classification:'Local Lean\nExactly five groupings',bridge:'Local Lean bridge\nExact graph witness',criterion:'Upstream Lean\nCompleted criterion',definitions:'Lean definitions\nAlgebra · congruence',target:'Comparator target\nContains sorry'};
    return [...Object.entries(positions).map(([id,[x,y]])=>({data:{id,label:names[id],kind:id==='target'?'target':'source'},position:{x,y}})), ...data.connections.map((c,i)=>({data:{id:`link-${i}`,...c}}))];
  }
  const api = {label,check,groupingResult,diagram,graphElements};
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  if (typeof document === 'undefined') return;
  const byId = id => document.getElementById(id), data = window.N5_CONTEXT;
  if (!data || data.id !== 'context:family-206:saved-n5:v1') {
    byId('context-error').hidden = false; byId('context-error').textContent = 'The saved N5 data could not be loaded. Open n5-context.json for the source record.'; return;
  }
  const values = data.claims[0].values, ops = values.operations, groups = values.groupings;
  byId('n5-diagram').innerHTML = diagram(groups);
  byId('operation-table').innerHTML = '<table><caption class="small">Exact saved outputs for each input</caption><thead><tr><th scope="col">Input</th>'+[0,1,2,3].map(x=>`<th scope="col">${x}</th>`).join('')+'</tr></thead><tbody>'+ops.map((op,i)=>`<tr><th scope="row">${'fg'[i]}(input)</th>${op.map(x=>`<td>${x}</td>`).join('')}</tr>`).join('')+'</tbody></table>';
  byId('partition-choice').innerHTML = data.partition_audit.map((r,i)=>`<option value="${i}">${esc(label(r.partition))}</option>`).join('');
  function showPartition() {
    const p = data.partition_audit[Number(byId('partition-choice').value)].partition;
    byId('partition-result').innerHTML = groupingResult(p,ops);
    byId('partition-result').classList.toggle('is-fail',Boolean(check(p,ops)));
  }
  byId('partition-choice').value = String(data.partition_audit.findIndex(r=>r.partition.join(',')==='0,1,2,2'));
  byId('partition-choice').addEventListener('change',showPartition); showPartition();
  byId('valid-table').innerHTML = '<table><thead><tr><th scope="col">Lattice label</th><th scope="col">Whole grouping</th></tr></thead><tbody>'+groups.map((g,i)=>`<tr><th scope="row">${['⊥ (bottom)','a','b','c','⊤ (top)'][i]}</th><td>${esc(label(g.partition))}</td></tr>`).join('')+'</tbody></table>';
  byId('color-table').innerHTML = '<table><caption class="small">d(x,y): the least valid grouping containing the pair</caption><thead><tr><th scope="col">x \\ y</th>'+[0,1,2,3].map(x=>`<th scope="col">${x}</th>`).join('')+'</tr></thead><tbody>'+data.color.map((row,i)=>`<tr><th scope="row">${i}</th>${row.map(c=>`<td>${esc(['⊥','a','b','c','⊤'][c])}</td>`).join('')}</tr>`).join('')+'</tbody></table>';
  byId('lean-statement').textContent = data.formal_statement;
  byId('paper-link').href = data.sources.find(s=>s.id==='paper').url;
  byId('source-choice').innerHTML = data.sources.map(s=>`<option value="${s.id}">${esc(s.title)}</option>`).join('');
  let cy;
  function showSource(id) {
    const s = data.sources.find(s=>s.id===id);
    byId('source-choice').value = id;
    byId('source-detail').innerHTML = `<h3>${esc(s.title)}</h3><span class="pill">${esc(s.role.replace(/_/g,' '))}</span><p>${esc(s.description)}</p><a href="${esc(s.url)}">Open this exact source ↗</a>${s.upstream_url?`<p><a href="${esc(s.upstream_url)}">Open the upstream original ↗</a></p>`:''}`;
    if (cy) { cy.elements().unselect(); cy.getElementById(id).select(); }
  }
  byId('source-choice').addEventListener('change',()=>showSource(byId('source-choice').value));
  byId('source-list').innerHTML = data.sources.map(s=>`<article id="source-${s.id}" class="source-row"><h4><a href="${esc(s.url)}">${esc(s.title)} ↗</a></h4><p>${esc(s.description)}</p>${s.sha256?`<code>SHA-256: ${s.sha256}</code>`:''}</article>`).join('');
  // Expand a source's containing disclosure when following a section link.
  function revealSource() { if (location.hash.startsWith('#source-')) { const el = byId(location.hash.slice(1)); if (el) { el.closest('details').open = true; el.scrollIntoView(); } } }
  window.addEventListener('hashchange',revealSource); revealSource();
  const relation = data.atlas_relation;
  byId('atlas-correspondence').innerHTML = `<p>The atlas entry <strong>${esc(relation.entry_id)}</strong> uses renamed objects. This checked mapping matches the grouping families:</p><p class="rule-display">Saved → atlas: ${relation.saved_to_atlas.map((v,i)=>`${i} → ${v}`).join(' · ')}</p><p>After renaming, the saved rules become <code>${esc(JSON.stringify(relation.transformed_saved_operations))}</code>. The atlas displays <code>${esc(JSON.stringify(relation.atlas_operations))}</code>. The rule tables differ.</p>`;
  if (typeof window.cytoscape === 'function') {
    const css = getComputedStyle(document.documentElement), color = key => css.getPropertyValue(key).trim();
    cy = window.cytoscape({container:byId('context-map'),elements:graphElements(data),layout:{name:'preset',padding:28},minZoom:.25,maxZoom:2,userZoomingEnabled:false,boxSelectionEnabled:false,autounselectify:false,
      style:[{selector:'node',style:{shape:'round-rectangle',width:205,height:62,'background-color':color('--graph-construction'),label:'data(label)',color:'#fff','text-wrap':'wrap','font-size':14,'text-valign':'center','text-halign':'center'}},{selector:'node[kind="target"]',style:{'background-color':color('--graph-shape')}},{selector:'edge',style:{label:'data(label)',width:2,'line-color':color('--graph-edge'),'target-arrow-color':color('--graph-edge'),'target-arrow-shape':'triangle','curve-style':'bezier','font-size':12,color:color('--ink'),'text-background-color':color('--ground'),'text-background-opacity':1,'text-background-padding':4}},{selector:'edge[kind="illustration"]',style:{'line-style':'dashed'}},{selector:'edge[kind="definition_reference"],edge[kind="comparison_reference"]',style:{'line-style':'dotted'}},{selector:'node:selected',style:{'border-width':4,'border-color':color('--graph-selected')}}]});
    cy.on('tap','node',event=>showSource(event.target.id()));
    byId('context-fit').addEventListener('click',()=>cy.fit(undefined,28));
    window.addEventListener('resize',()=>{cy.resize();cy.fit(undefined,28);});
  } else {byId('map-unavailable').hidden=false;byId('context-fit').disabled=true;}
  showSource('target');
})();
