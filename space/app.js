/* The explorer displays recorded checks; only relation filtering happens here. */
"use strict";
const COLORS = ["#667580", "#147e70", "#4263ad", "#b26525", "#9968a3", "#b64d62", "#698033", "#263f54"];
const NAMES = {C2:"Two-element chain",C3:"Three-element chain",C4:"Four-element chain",B2:"Boolean square",M3:"Three-atom diamond",N5:"Pentagon",M4:"Four-atom diamond",B3:"Boolean cube"};
const SHORT = {C2:"chain",C3:"chain",C4:"chain",B2:"square",M3:"diamond",N5:"pentagon",M4:"diamond",B3:"cube"};
function escapeHtml(value) { return String(value).replace(/[&<>"']/g, x => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"})[x]); }
function connectedBlocks(size, edges) {
  const remaining = new Set(Array.from({length:size},(_,i)=>i)), result=[];
  while(remaining.size) {
    const start=remaining.values().next().value, group=[start]; remaining.delete(start);
    for(let k=0;k<group.length;k++) for(const [u,v] of edges) {
      const other=u===group[k]?v:v===group[k]?u:-1;
      if(remaining.has(other)){remaining.delete(other);group.push(other);}
    }
    result.push(group.sort((a,b)=>a-b));
  }
  return result;
}
function thresholdEdges(color,leq,element) {
  const edges=[];
  for(let i=0;i<color.length;i++) for(let j=i+1;j<color.length;j++) if(leq[color[i][j]][element]) edges.push([i,j]);
  return edges;
}
function carrierPositions(n) {
  if(n===1)return [[150,110]];
  if(n===2)return [[75,110],[225,110]];
  if(n===3)return [[150,32],[55,178],[245,178]];
  return [[65,40],[235,40],[235,180],[65,180]];
}
function svgFrame(title,body) {return `<svg viewBox="0 0 300 220" role="img" aria-label="${escapeHtml(title)}"><title>${escapeHtml(title)}</title>${body}</svg>`;}
function graphSvg(example,lattice,threshold,overrideEdges=null) {
  const pos=carrierPositions(example.vertices), edges=[],labels=[];
  for(let i=0;i<pos.length;i++) for(let j=i+1;j<pos.length;j++) {
    const color=example.color[i][j], active=overrideEdges?overrideEdges.some(([a,b])=>(a===i&&b===j)||(b===i&&a===j)):lattice.leq[color][threshold];
    if(overrideEdges && !active)continue;
    const [x,y]=pos[i], [xx,yy]=pos[j];
    edges.push(`<line x1="${x}" y1="${y}" x2="${xx}" y2="${yy}" stroke="${active?(overrideEdges?'#92520a':COLORS[color%COLORS.length]):'#dce3de'}" stroke-width="${active?2.6:1.2}" ${active?'':'stroke-dasharray="4 4"'}/>`);
    if(!overrideEdges){
      let t=pos.length===4&&j-i===2?(i===0?.34:.65):.5;
      const lx=x+(xx-x)*t, ly=y+(yy-y)*t, label=escapeHtml(lattice.elements[color]), w=Math.max(20,lattice.elements[color].length*8+10);
      labels.push(`<rect x="${lx-w/2}" y="${ly-10}" width="${w}" height="20" rx="5" fill="#fbfcfa"/><text x="${lx}" y="${ly+4}" text-anchor="middle" font-size="12" style="fill:#112c3c">${label}</text>`);
    }
  }
  const nodes=pos.map(([x,y],i)=>`<circle cx="${x}" cy="${y}" r="17" fill="#112c3c"/><text x="${x}" y="${y+5}" text-anchor="middle" font-size="13" style="fill:white">${i}</text>`).join('');
  const title=overrideEdges?`Generated seed graph on ${pos.length} vertices. Edges: ${overrideEdges.map(e=>e.join('–')).join(', ')||'none'}.`:`${lattice.id} colored graph on ${pos.length} vertices, filtered at ${lattice.elements[threshold]}. Full edge labels are available in the color matrix.`;
  return svgFrame(title,edges.join('')+labels.join('')+nodes);
}
function latticeSvg(lattice,threshold) {
  const max=Math.max(...lattice.ranks), levels=Array.from({length:max+1},()=>[]);
  lattice.ranks.forEach((r,i)=>levels[r].push(i));
  const pos=[];
  levels.forEach((group,r)=>group.forEach((id,j)=>{pos[id]=[300*(j+1)/(group.length+1),185-(max?r/max:0)*150];}));
  const edges=lattice.covers.map(([i,j])=>`<line x1="${pos[i][0]}" y1="${pos[i][1]}" x2="${pos[j][0]}" y2="${pos[j][1]}" stroke="#bac8be" stroke-width="2"/>`).join('');
  const nodes=pos.map(([x,y],i)=>`<circle cx="${x}" cy="${y}" r="${i===threshold?14:10}" fill="${i===threshold?'#096d62':lattice.leq[i][threshold]?'#dcefe5':'#f4f6f1'}" stroke="${i===threshold?'#096d62':'#899e91'}" stroke-width="1.4"/><text x="${x}" y="${y+4}" font-size="${lattice.elements[i].length>2?10:12}" text-anchor="middle" style="fill:${i===threshold?'white':'#112c3c'}">${escapeHtml(lattice.elements[i])}</text>`).join('');
  return svgFrame(`${lattice.id} lattice. Cover relations: ${lattice.covers.map(([i,j])=>`${lattice.elements[i]} below ${lattice.elements[j]}`).join('; ')}.`,edges+nodes);
}
function blocksText(blocks){return blocks.map(b=>`{${b.join(', ')}}`).join(' · ');}
function matrixHtml(example,lattice){return `<table><caption>Full symmetric edge-color matrix; diagonal entries are the bottom element.</caption><thead><tr><th scope="col">Point</th>${example.color.map((_,i)=>`<th scope="col">${i}</th>`).join('')}</tr></thead><tbody>${example.color.map((row,i)=>`<tr><th scope="row">${i}</th>${row.map(c=>`<td>${escapeHtml(lattice.elements[c])}</td>`).join('')}</tr>`).join('')}</tbody></table>`;}
if(typeof module!=="undefined" && module.exports) module.exports={connectedBlocks,thresholdEdges,carrierPositions,escapeHtml,graphSvg,latticeSvg};
if(typeof document!=="undefined") {
  const $=id=>document.getElementById(id), fmt=x=>Number(x).toLocaleString('en-US');
  let data,selected,mode="passing",threshold;
  const getFailure=()=>data.failure_examples.find(x=>x.lattice_id===selected.id);
  const getExample=()=>mode==='passing'?selected.witness:getFailure();
  function renderRelation(){
    const example=getExample();
    $('lattice-diagram').innerHTML=latticeSvg(selected,threshold);
    if(!example){$('carrier-diagram').textContent='No passing witness recorded within the search bound.';return;}
    $('carrier-diagram').innerHTML=graphSvg(example,selected,threshold);
    const blocks=connectedBlocks(example.vertices,thresholdEdges(example.color,selected.leq,threshold));
    $('relation-result').textContent=`At ${selected.elements[threshold]}: ${blocksText(blocks)} — ${blocks.length} equivalence ${blocks.length===1?'class':'classes'} on ${example.vertices} carrier points.`;
  }
  function render(){
    const example=getExample(),bad=mode==='failing';
    document.querySelectorAll('[data-lattice]').forEach(button=>button.setAttribute('aria-pressed',String(button.dataset.lattice===selected.id)));
    $('lattice-name').textContent=selected.id;
    $('lattice-description').textContent=NAMES[selected.id];
    const stats=selected.stats.aggregate;
    $('lattice-facts').innerHTML=[['Lattice elements',selected.elements.length],['Smallest carrier',selected.stats.minimum_vertices??'None ≤ 4'],['Full witnesses',fmt(stats.witnesses)],['Candidate colorings',fmt(stats.candidates)]].map(([label,value])=>`<div><dt>${label}</dt><dd>${value}</dd></div>`).join('');
    $('passing').disabled=!selected.witness; $('failing').disabled=!getFailure();
    $('passing').setAttribute('aria-pressed',String(!bad));$('failing').setAttribute('aria-pressed',String(bad));
    $('case-help').textContent=!selected.witness?'No passing witness was found on 1–4 points. The failing example shows one obstruction.':!getFailure()?'All structural survivors passed connectivity for this lattice within the tested bound.':'Compare a saved witness with a structural survivor that fails seed connectivity.';
    $('case-title').textContent=bad?`${selected.id} · A connectivity obstruction`:`${selected.id} · A minimum-carrier witness`;
    $('case-status').textContent=bad?'Connectivity failed':'All 5 conditions passed';$('case-status').className='status'+(bad?' fail':'');
    $('case-summary').textContent=bad?'Replayed demonstration: the first four conditions hold, but a required path is missing.':`${example.vertices} carrier points · ${example.verification.admissible_self_maps} admissible unary maps · ${fmt(example.verification.nonempty_ordered_seed_subsets_enumerated)} ordered seed subsets checked.`;
    $('download').href=example.certificate;
    $('download').textContent=bad?'Download failing example ↓':'Download certificate ↓';
    $('source-link').href=bad?`${data.provenance.repository}/blob/main/space/${example.certificate}`:`${data.provenance.repository}/blob/${data.provenance.source_commit}/evidence/${selected.id}-witness.json`;
    $('relation').innerHTML=selected.elements.map((label,i)=>`<option value="${i}">${escapeHtml(label)}</option>`).join('');$('relation').value=String(threshold);
    $('matrix').innerHTML=matrixHtml(example,selected);
    $('color-key').innerHTML=selected.elements.map((label,i)=>`<span><i class="swatch" style="background:${COLORS[i%COLORS.length]}"></i>${escapeHtml(label)}</span>`).join('');
    $('failure').hidden=!bad;
    if(bad){
      const f=example.failure;
      const edges=f.marked_pairs.filter(([u,v])=>u!==v);
      const groups=connectedBlocks(example.vertices,edges);
      $('failure').innerHTML=`<h4>Why this example fails</h4><p>Seed pairs ${f.ordered_seeds.map(p=>`(${p.join(', ')})`).join(', ')} have joined color <strong>${escapeHtml(selected.elements[f.join_bound])}</strong>. Applying every admissible map to these seeds gives the graph below.</p><div class="diagram">${graphSvg(example,selected,threshold,edges)}</div><p>Its connected components are <strong>${blocksText(groups)}</strong>. The required pair <strong>(${f.endpoints.join(', ')})</strong> has color at or below the joined bound, yet its endpoints are disconnected.</p><p class="small">This rejects this graph as a witness. It is not a proof that the lattice has no representation on other carriers.</p>`;
      $('operations').innerHTML='';
    }else{
      const ops=example.operations;
      $('operations').innerHTML=`<h4>${ops.minimum_count} selected unary ${ops.minimum_count===1?'operation':'operations'} suffice for these exact relations</h4>${ops.selected_tables.map((op,i)=>`<code>f${i+1} = [${op.join(', ')}]</code>`).join('')}<p>${ops.minimum_count?'Each list gives the image of points 0, 1, … in order.':'The empty operation signature already has exactly the required equivalence relations.'} The full admissible pool has ${ops.admissible_count} maps. Minimality is for this saved representation.</p>`;
    }
    renderRelation();
  }
  function choose(id){selected=data.lattices.find(x=>x.id===id);mode=selected.witness?'passing':'failing';threshold=selected.top;render();}
  async function init(){
    try{
      const response=await fetch('data.json');if(!response.ok)throw new Error('Data unavailable');data=await response.json();
      if(data.schema_version!==1||!Array.isArray(data.lattices)||!Array.isArray(data.failure_examples))throw new Error('Unrecognized data');
      $('lattice-picker').innerHTML=data.lattices.map(l=>`<button type="button" data-lattice="${l.id}" aria-pressed="false">${l.id}<span>${SHORT[l.id]}</span></button>`).join('');
      $('lattice-picker').addEventListener('click',e=>{const button=e.target.closest('[data-lattice]');if(button)choose(button.dataset.lattice);});
      $('passing').addEventListener('click',()=>{mode='passing';threshold=selected.top;render();});
      $('failing').addEventListener('click',()=>{mode='failing';threshold=selected.top;render();});
      $('relation').addEventListener('change',e=>{threshold=Number(e.target.value);renderRelation();});
      $('total-candidates').textContent=fmt(data.totals.candidates);$('total-witnesses').textContent=fmt(data.totals.witnesses);$('total-classes').textContent=fmt(data.totals.vertex_isomorphism_classes);
      $('results-table').innerHTML=`<table><caption class="sr-only">Search results across carriers of one through four points</caption><thead><tr>${['Lattice','Candidates','Structural survivors','Full witnesses','Vertex classes','Smallest carrier'].map(h=>`<th scope="col">${h}</th>`).join('')}</tr></thead><tbody>${data.lattices.map(l=>{const s=l.stats.aggregate;return `<tr><th scope="row">${l.id} <span class="small">· ${SHORT[l.id]}</span></th><td>${fmt(s.candidates)}</td><td>${fmt(s.structural??s.structural_survivors)}</td><td>${fmt(s.witnesses)}</td><td>${fmt(s.classes??s.vertex_isomorphism_classes)}</td><td>${l.stats.minimum_vertices??'None ≤ 4'}</td></tr>`;}).join('')}</tbody></table>`;
      $('provenance').innerHTML=`<p>Evidence snapshot: <a href="${data.provenance.repository}/tree/${data.provenance.source_commit}" target="_blank" rel="noopener noreferrer"><code>${data.provenance.source_commit}</code></a></p><p>Upstream: <a href="${data.provenance.upstream.url}" target="_blank" rel="noopener noreferrer">OpenAI math, family 206</a> at <code>${data.provenance.upstream.revision}</code>.</p><p>Passing certificates are copied byte for byte from the research evidence. Failing demonstrations are derived from recorded negative samples and replayed with the independent checker. Every source file’s SHA-256 is listed in the downloadable explorer data.</p>`;
      choose('N5');$('app').hidden=false;$('loading').hidden=true;
    }catch(error){$('loading').className='error';$('loading').innerHTML='The evidence could not be loaded. Reload this page, or <a href="https://github.com/Maverick0351a/finite-congruence-checks">open the original results on GitHub</a>.';console.error('Explorer initialization failed:',error.message);}
  }
  init();
}
