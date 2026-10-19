/* Display registered proof transfers. Browser equations are illustrations, not Lean execution. */
(function () {
  'use strict';
  const esc = value => String(value).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const names = ['⊥ · everything separate', 'a · one pair', 'b · two neighboring pairs', 'c · two alternating pairs', '⊤ · everything together'];
  const sourceRule = index => ['f', 'g'][index];
  const targetRule = index => `target rule ${index + 1}`;
  function blocks(partition) {
    const result = new Map();
    partition.forEach((group, object) => {
      if (!result.has(group)) result.set(group, []);
      result.get(group).push(object);
    });
    return [...result.values()];
  }
  const label = partition => blocks(partition).map(group => `{${group.join(', ')}}`).join(' | ');
  function groupingFailure(partition, operations) {
    for (let rule = 0; rule < operations.length; rule++) {
      for (let x = 0; x < partition.length; x++) for (let y = x + 1; y < partition.length; y++) {
        if (partition[x] === partition[y] && partition[operations[rule][x]] !== partition[operations[rule][y]]) {
          return {rule, pair: [x, y], outputs: [operations[rule][x], operations[rule][y]]};
        }
      }
    }
    return null;
  }
  function route(claim, rule, object, ruleMap = claim.mapping.rule_target_to_source) {
    const p = claim.mapping.object_forward_source_to_target;
    const sourceOutput = claim.values.source.operations[ruleMap[rule]][object];
    const targetObject = p[object], expectedOutput = p[sourceOutput];
    const targetOutput = claim.values.target.operations[rule][targetObject];
    return {rule, source_rule: ruleMap[rule], source_object: object, source_output: sourceOutput,
      target_object: targetObject, target_output: targetOutput, expected_output: expectedOutput,
      agrees: targetOutput === expectedOutput};
  }
  function correspondenceFailure(claim, ruleMap) {
    for (let rule = 0; rule < 2; rule++) for (let x = 0; x < 4; x++) {
      const step = route(claim, rule, x, ruleMap);
      if (!step.agrees) return step;
    }
    return null;
  }
  function pairedGroups(claim, index) {
    const source = claim.values.source.groupings[index];
    const targetIndex = claim.mapping.grouping_source_to_target[index];
    const target = claim.values.target.groupings[targetIndex];
    const inverse = claim.mapping.object_backward_target_to_source;
    const sourceBlocks = blocks(source);
    return {
      source: sourceBlocks.map((objects, group) => ({group, objects, source_objects: objects})),
      target: blocks(target).map(objects => ({
        group: sourceBlocks.findIndex(block => block.includes(inverse[objects[0]])),
        objects, source_objects: objects.map(x => inverse[x]),
      })),
      source_partition: source, target_partition: target,
    };
  }
  function groupMarkup(groups, selected, side) {
    return groups.map(block => `<div class="reuse-block reuse-group-${block.group}"><span class="reuse-block-name">Group ${String.fromCharCode(65 + block.group)}</span><div>${block.objects.map((object, i) => `<button type="button" class="reuse-object" data-source-object="${block.source_objects[i]}" aria-pressed="${block.source_objects[i] === selected}" aria-label="${side === 'source' ? 'Original' : 'Renamed'} object ${object}, corresponding original object ${block.source_objects[i]}">${object}</button>`).join('')}</div></div>`).join('');
  }
  function operationTable(operations, selected, side, ruleMap) {
    return `<table><caption>${side === 'source' ? 'Original' : 'Renamed'} operation outputs</caption><thead><tr><th scope="col">Input</th>${[0,1,2,3].map(x => `<th scope="col"${x === selected ? ' class="reuse-highlight"' : ''}>${x}</th>`).join('')}</tr></thead><tbody>${operations.map((operation, index) => `<tr><th scope="row">${side === 'source' ? sourceRule(index) : `Rule ${index + 1}<small>from ${sourceRule(ruleMap[index])}</small>`}</th>${operation.map((output, x) => `<td${x === selected ? ' class="reuse-highlight"' : ''}>${output}</td>`).join('')}</tr>`).join('')}</tbody></table>`;
  }
  function square(step) {
    const description = `Original object ${step.source_object} goes to ${step.source_output} under ${sourceRule(step.source_rule)}. Renaming sends them to ${step.target_object} and ${step.expected_output}. Target rule ${step.rule + 1} sends ${step.target_object} to ${step.target_output}. ${step.agrees ? 'The two routes agree.' : 'The routes disagree.'}`;
    return `<svg viewBox="0 0 440 260" role="img" aria-label="${esc(description)}"><defs><marker id="reuse-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z"/></marker></defs><path class="reuse-arrow" d="M 105 50 H 335 M 105 205 H 335 M 70 82 V 172 M 370 82 V 172"/><text x="220" y="35" text-anchor="middle">original ${sourceRule(step.source_rule)}</text><text x="220" y="240" text-anchor="middle">target rule ${step.rule + 1}</text><text x="115" y="133">rename</text><text x="265" y="133">rename</text>${[[70,50,step.source_object],[370,50,step.source_output],[70,205,step.target_object],[370,205,step.target_output]].map(([x,y,v]) => `<circle cx="${x}" cy="${y}" r="28"/><text class="reuse-square-object" x="${x}" y="${y + 7}" text-anchor="middle">${v}</text>`).join('')}</svg>`;
  }
  function proofSteps(transfer) {
    const claim = transfer.record.claim;
    const p = claim.mapping.object_forward_source_to_target;
    return [
      {id:'original',title:'Original construction',label:'Original\nexact saved N5',url:transfer.links.construction,
        description:`The source is ${claim.source_construction_id}. Its exact two rules have a separate classification proof.`,detail:claim.source_claim_id},
      {id:'mapping',title:'Consistent mapping',label:'Object + rule\ncorrespondence',url:transfer.links.claim,
        description:`Rename ${p.map((v,i) => `${i} → ${v}`).join(', ')}. Every target rule must agree with its mapped source rule on every object.`,detail:`Target rules 1, 2 come from source ${claim.mapping.rule_target_to_source.map(sourceRule).join(', ')}.`},
      {id:'claim',title:'Exact target claim',label:'Target claim\nexactly five groupings',url:transfer.links.claim,
        description:claim.statement,detail:claim.id},
      {id:'proof',title:'Applicable Lean theorem',label:'Lean theorem\nclassification + transport',url:transfer.links.proof,
        description:'The proof transports the source classification through this bijection. Separate lemmas preserve inclusion order and show that the five groupings are distinct.',detail:claim.theorem},
    ];
  }
  function graphElements(transfer, width = 600) {
    const positions = width < 500 ? [[120,45],[120,155],[120,265],[120,375]] : [[120,65],[390,65],[390,245],[120,245]];
    const nodes = proofSteps(transfer).map((step,i) => ({data:{id:step.id,label:step.label},position:{x:positions[i][0],y:positions[i][1]}}));
    return [...nodes,
      {data:{id:'rename',source:'original',target:'mapping',label:'renamed using'}},
      {data:{id:'specify',source:'mapping',target:'claim',label:'specifies the target'}},
      {data:{id:'justify',source:'claim',target:'proof',label:'proved by'}},
    ];
  }
  function controlMarkup(control, transfers) {
    const transfer = transfers.find(t => t.key === control.transfer);
    if (!transfer) throw new Error('Control refers to an unknown transfer');
    const claim = transfer.record.claim;
    let details;
    if (control.category === 'grouping_failure') {
      const failure = groupingFailure(control.partition,control.operations);
      if (!failure) throw new Error('The grouping-failure example has no violating pair');
      details = `<p>Start with the <strong>${esc(transfer.title)}</strong> example, but keep the original rules. The renamed grouping ${esc(label(control.partition))} puts ${failure.pair.join(' and ')} together.</p><p class="reuse-witness">${sourceRule(failure.rule)}(${failure.pair[0]}) = ${failure.outputs[0]} &nbsp; · &nbsp; ${sourceRule(failure.rule)}(${failure.pair[1]}) = ${failure.outputs[1]}</p><p>Those outputs are separate. This exact pair witnesses a mathematical failure under the unchanged rules.</p>`;
    } else if (control.category === 'correspondence_failure') {
      const failure = correspondenceFailure(claim,control.rule_map);
      if (!failure) throw new Error('The correspondence-failure example has no violated equation');
      details = `<p>Use <strong>${esc(transfer.title)}</strong>, but claim that target rule ${failure.rule + 1} comes from source ${sourceRule(failure.source_rule)}.</p><p class="reuse-witness">Rename after ${sourceRule(failure.source_rule)}: ${failure.source_object} → ${failure.source_output} → ${failure.expected_output}<br>Target rule after renaming: ${failure.source_object} → ${failure.target_object} → ${failure.target_output}</p><p>The final objects differ. The target operations and five valid groupings remain unchanged; the declared rule correspondence is wrong. This does <strong>not</strong> refute the target classification.</p>`;
    } else if (control.category === 'unsupported_evidence') {
      details = `<p>Keep the valid <strong>${esc(transfer.title)}</strong> construction, but substitute <code>${esc(control.proposed_theorem)}</code>.</p><p>The B3 theorem has a different subject. It does not supply the required classification of this N5 construction. The registered binding expects <code>${esc(claim.theorem)}</code>.</p><p>This leaves the proposed evidence unsupported. It does <strong>not</strong> make the N5 statement false.</p><p class="caption">The repository's negative binding check rejects this substitution. This browser explanation does not elaborate or type-check Lean.</p>`;
    } else { throw new Error('Unknown demonstration category'); }
    return `<article class="reuse-outcome ${esc(control.category)}"><span class="reuse-outcome-kind">${esc(control.category.replace(/_/g,' '))}</span><h4>${esc(control.title)}</h4>${details}</article>`;
  }
  const api = {blocks,label,groupingFailure,route,correspondenceFailure,pairedGroups,groupMarkup,operationTable,square,proofSteps,graphElements,controlMarkup};
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  if (typeof document === 'undefined') return;
  const byId = id => document.getElementById(id), data = window.N5_REUSE;
  function fail(message) { byId('reuse-error').hidden = false; byId('reuse-error').textContent = `${message} Open n5-reuse.json to inspect the saved records.`; }
  if (!data || data.id !== 'context:family-206:proof-reuse-demo:v1' || !Array.isArray(data.transfers) || data.transfers.length !== 2) {
    fail('The proof-reuse records could not be loaded.'); return;
  }
  let transfer, cy;
  function mapElements() {
    const container = byId('reuse-map'), width = container.clientWidth;
    container.classList.toggle('reuse-map-stacked',width < 500);
    return graphElements(transfer,width);
  }
  function relayoutMap() {
    const selected = byId('reuse-evidence').value || 'claim';
    cy.elements().remove(); cy.add(mapElements()); cy.resize();
    cy.layout({name:'preset',padding:30}).run();
    cy.getElementById(selected).select();
  }
  byId('reuse-transfer').innerHTML = data.transfers.map(t => `<option value="${esc(t.key)}">${esc(t.title)}</option>`).join('');
  byId('reuse-transfer').value = data.default_transfer;
  byId('reuse-grouping').innerHTML = names.map((name,i) => `<option value="${i}">${esc(name)}</option>`).join('');
  byId('reuse-grouping').value = '1';
  byId('reuse-mistake').innerHTML = data.controls.map(c => `<option value="${esc(c.id)}">${esc(c.title)}</option>`).join('');
  function showEvidence(id) {
    const step = proofSteps(transfer).find(s => s.id === id);
    byId('reuse-evidence').value = id;
    byId('reuse-evidence-detail').innerHTML = `<h3>${esc(step.title)}</h3><p>${esc(step.description)}</p><p><code>${esc(step.detail)}</code></p><a href="${esc(step.url)}">Open this exact reference ↗</a>${id === 'proof' ? `<p class="reuse-receipt-link"><a href="${esc(transfer.links.receipt)}">Inspect the separate verification receipt ↗</a></p><p class="caption">Saved evidence identifies the checked source and build. This page does not rerun Lean.</p>` : ''}`;
    if (cy) { cy.elements().unselect(); cy.getElementById(id).select(); }
  }
  function showRoute() {
    const step = route(transfer.record.claim,Number(byId('reuse-rule').value),Number(byId('reuse-object').value));
    byId('reuse-route-text').textContent = `${sourceRule(step.source_rule)}(${step.source_object}) = ${step.source_output}; renaming gives ${step.expected_output}. ${targetRule(step.rule)}(${step.target_object}) = ${step.target_output}. ${step.agrees ? 'The two routes agree.' : 'The recorded equation does not agree.'}`;
    byId('reuse-square').innerHTML = square(step);
  }
  function showGrouping() {
    const claim = transfer.record.claim, selected = Number(byId('reuse-object').value);
    const paired = pairedGroups(claim,Number(byId('reuse-grouping').value));
    byId('reuse-source-groups').innerHTML = groupMarkup(paired.source,selected,'source');
    byId('reuse-target-groups').innerHTML = groupMarkup(paired.target,selected,'target');
    byId('reuse-source-rules').innerHTML = operationTable(claim.values.source.operations,selected,'source',claim.mapping.rule_target_to_source);
    byId('reuse-target-rules').innerHTML = operationTable(claim.values.target.operations,claim.mapping.object_forward_source_to_target[selected],'target',claim.mapping.rule_target_to_source);
    byId('reuse-correspondence').textContent = `${label(paired.source_partition)} becomes ${label(paired.target_partition)}. Group letters identify matching blocks. Highlighted original object ${selected} corresponds to renamed object ${claim.mapping.object_forward_source_to_target[selected]}.`;
    showRoute();
  }
  function showControl() {
    const control = data.controls.find(c => c.id === byId('reuse-mistake').value);
    byId('reuse-mistake-result').innerHTML = controlMarkup(control,data.transfers);
  }
  function showTransfer() {
    transfer = data.transfers.find(t => t.key === byId('reuse-transfer').value);
    const claim = transfer.record.claim;
    const selectedObject = byId('reuse-object').value || '0';
    byId('reuse-object').innerHTML = claim.mapping.object_forward_source_to_target.map((target,original) => `<option value="${original}">Original ${original} ↔ renamed ${target}</option>`).join('');
    byId('reuse-object').value = selectedObject;
    byId('reuse-rule').innerHTML = claim.mapping.rule_target_to_source.map((source,index) => `<option value="${index}">Target rule ${index + 1} · from original ${sourceRule(source)}</option>`).join('');
    byId('reuse-description').textContent = transfer.description;
    byId('reuse-evidence').innerHTML = proofSteps(transfer).map(step => `<option value="${step.id}">${esc(step.title)}</option>`).join('');
    byId('reuse-download').href = transfer.download;
    byId('reuse-query-command').textContent = `python scripts/query_context.py explain ${claim.id} --out n5-reuse-query.json\npython scripts/query_context.py check n5-reuse-query.json`;
    byId('reuse-claim-details').innerHTML = `<p><strong>Exact construction:</strong> <code>${esc(claim.construction_id)}</code></p><p><strong>Classification theorem:</strong> <code>${esc(claim.theorem)}</code></p><p><strong>Statement:</strong> ${esc(claim.statement)}</p><h4>Assumptions</h4><ul>${claim.assumptions.map(a => `<li>${esc(a)}</li>`).join('')}</ul><h4>What each lemma supports</h4><ul>${claim.applicable_lemmas.map(l => `<li><code>${esc(l.theorem)}</code> — ${esc(l.role.replace(/_/g,' '))}</li>`).join('')}</ul><h4>Limits</h4><ul>${claim.limits.map(l => `<li>${esc(l)}</li>`).join('')}</ul>`;
    if (cy) relayoutMap();
    showGrouping(); showEvidence('claim');
  }
  try {
    showTransfer(); showControl(); byId('reuse-content').hidden = false;
    if (typeof window.cytoscape === 'function') {
      const css = getComputedStyle(document.documentElement), color = name => css.getPropertyValue(name).trim();
      cy = window.cytoscape({container:byId('reuse-map'),elements:mapElements(),layout:{name:'preset',padding:30},minZoom:.25,maxZoom:2,userZoomingEnabled:false,boxSelectionEnabled:false,
        style:[{selector:'node',style:{shape:'round-rectangle',width:190,height:62,'background-color':color('--graph-construction'),label:'data(label)',color:'#fff','text-wrap':'wrap','font-size':14,'text-valign':'center','text-halign':'center'}},{selector:'node[id="proof"]',style:{'background-color':color('--graph-shape')}},{selector:'edge',style:{label:'data(label)',width:2,'line-color':color('--graph-edge'),'target-arrow-color':color('--graph-edge'),'target-arrow-shape':'triangle','curve-style':'bezier','font-size':11,color:color('--ink'),'text-background-color':color('--ground'),'text-background-opacity':1,'text-background-padding':5}},{selector:'node:selected',style:{'border-width':4,'border-color':color('--graph-selected')}}]});
      cy.on('tap','node',event => showEvidence(event.target.id()));
      byId('reuse-fit').addEventListener('click',() => cy.fit(undefined,30));
      window.addEventListener('resize',relayoutMap);
      showEvidence('claim');
    } else { byId('reuse-map-unavailable').hidden = false; byId('reuse-fit').disabled = true; }
    byId('reuse-transfer').addEventListener('change',showTransfer);
    byId('reuse-grouping').addEventListener('change',showGrouping);
    byId('reuse-object').addEventListener('change',showGrouping);
    byId('reuse-rule').addEventListener('change',showRoute);
    byId('reuse-mistake').addEventListener('change',showControl);
    byId('reuse-evidence').addEventListener('change',() => showEvidence(byId('reuse-evidence').value));
    for (const id of ['reuse-source-groups','reuse-target-groups']) byId(id).addEventListener('click',event => {
      const button = event.target.closest('button[data-source-object]');
      if (button) {
        const selected = button.dataset.sourceObject;
        byId('reuse-object').value = selected; showGrouping();
        byId(id).querySelector(`[data-source-object="${selected}"]`).focus();
      }
    });
  } catch (error) { fail('The proof-reuse display could not be checked.'); byId('reuse-content').hidden = true; }
})();
