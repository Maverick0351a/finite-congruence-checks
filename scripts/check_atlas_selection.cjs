/* Deterministic event-wiring and data checks. This DOM fixture is NOT a browser. */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const {checkAtlasContrast} = require('./check_atlas_contrast.cjs');
const root = path.resolve(process.argv[2] || path.join(__dirname, '..'));
const read = name => fs.readFileSync(path.join(root, name), 'utf8');
const data = JSON.parse(read('space/atlas-data.json'));
const registry = JSON.parse(read('space/atlas-claims.json'));
const cytoscape = require(path.join(root, 'space/vendor/cytoscape-3.34.4.min.js'));
const app = require(path.join(root, 'space/atlas.js'));
const html = read('space/atlas.html');
const charts = [];
let checks = 0;
function same(actual, expected, message) { checks++; assert.deepEqual(actual, expected, message); }
function ok(value, message) { checks++; assert(value, message); }
function fixture(search = '', renderer = 'cytoscape') {
  const nodes = new Map(), downloads = [], clipboardCopies = [], blobs = new Map();
  const document = { activeElement: null };
  class Node {
    constructor(tag = 'div', attrs = {}) {
      this.tagName = tag; this.attrs = attrs; this.id = attrs.id; this.events = new Map(); this.children = [];
      this.value = attrs.value || ''; this.dataset = {}; this.hidden = false; this.disabled = false;
      for (const [key, value] of Object.entries(attrs)) if (key.startsWith('data-')) this.dataset[key.slice(5)] = value;
      this.classList = { toggle() {} }; this.textContent = ''; this._html = '';
    }
    set innerHTML(value) {
      this._html = value; this.children = [];
      for (const match of value.matchAll(/<(button|option)\b([^>]*)>([\s\S]*?)<\/\1>/g)) {
        const attrs = Object.fromEntries([...match[2].matchAll(/([\w-]+)="([^"]*)"/g)].map(m => [m[1], m[2]]));
        const child = new Node(match[1], attrs); child.textContent = match[3]; this.children.push(child);
      }
    }
    get innerHTML() { return this._html; }
    addEventListener(type, callback) { this.events.set(type, [...(this.events.get(type) || []), callback]); }
    dispatch(type) { for (const callback of this.events.get(type) || []) callback({ target: this }); }
    click() { if (this.disabled) return; this.dispatch('click'); if (this.download) downloads.push({ name: this.download, text: blobs.get(this.href).parts.join('') }); }
    setAttribute(key, value) { this.attrs[key] = value; }
    getAttribute(key) { return this.attrs[key]; }
    querySelectorAll(selector) { assert.equal(selector, 'button'); return this.children.filter(child => child.tagName === 'button'); }
    closest(selector) { assert.equal(selector, '.entry-detail'); return document.detail; }
    insertAdjacentHTML(position, value) { assert.equal(position, 'beforeend'); this.innerHTML = this.innerHTML + value; }
    replaceChildren() { this.innerHTML = ''; }
    focus() { document.activeElement = this; }
    scrollIntoView() { this.scrolled = true; }
    append() {}
    remove() {}
  }
  for (const match of html.matchAll(/<([\w-]+)\b([^>]*\bid="([^"]+)"[^>]*)>/g)) nodes.set(match[3], new Node(match[1], {id:match[3]}));
  for (const match of html.matchAll(/<select\b[^>]*id="([^"]+)"[^>]*>([\s\S]*?)<\/select>/g)) {
    const node = nodes.get(match[1]); node.innerHTML = match[2];
    node.value = /value="([^"]+)" selected/.exec(match[2])?.[1] || node.children[0]?.value || '';
  }
  document.detail = new Node('article'); document.body = new Node('body');
  document.getElementById = id => { assert(nodes.has(id), `Missing DOM fixture id ${id}`); return nodes.get(id); };
  document.querySelectorAll = selector => { assert.equal(selector, '[data-lesson]'); return []; };
  document.createElement = tag => new Node(tag); document.documentElement = new Node('html');
  let chart;
  const window = {
    ATLAS_DATA: data, ATLAS_CLAIMS: registry, location: {search}, addEventListener() {},
    matchMedia: () => ({matches:true, addEventListener() {}}),
  };
  // Transfer plain graph options out of the VM realm; no browser layout is simulated.
  if (renderer === 'cytoscape') window.cytoscape = options => { chart = cytoscape({...JSON.parse(JSON.stringify({...options,container:undefined})), headless:true, styleEnabled:false}); charts.push(chart); return chart; };
  if (renderer === 'throws') window.cytoscape = () => { throw new Error('Injected renderer failure'); };
  const navigator = {clipboard: {writeText(text) {clipboardCopies.push(text); return Promise.resolve();}}};
  const context = vm.createContext({window, document, navigator, URLSearchParams, Blob:class {constructor(parts) {this.parts=parts;}}, URL:{createObjectURL(blob) { const id=`blob:fixture-${blobs.size}`; blobs.set(id,blob); return id; },revokeObjectURL() {}}, getComputedStyle:() => ({getPropertyValue:()=>'#111111'})});
  for (const name of ['atlas-map.js','atlas.js']) vm.runInContext(read(`space/${name}`), context, {filename:name});
  const get = id => nodes.get(id);
  const change = (id, value) => { get(id).value = value; get(id).dispatch('change'); };
  function expectEntry(id) {
    same(get('map-entry').value, id, 'Map selector matches detail selection');
    ok(get('entry-kicker').textContent.includes(id), 'Detail matches selection');
    const record = JSON.parse(get('entry-json').textContent);
    same(record.entry.id, id, 'Certificate preview matches selection');
    ok(get('entry-claims').innerHTML.includes(`construction:${id}`), 'Inspector contains exact construction claim');
    ok(get('entry-claims').innerHTML.includes(`minimum:${id}`), 'Inspector contains separate minimum claim');
    same(get('map-carrier').value, get('carrier-filter').value, 'Carrier filters mirror');
    same(get('map-shape').value, get('shape-filter').value, 'Shape filters mirror');
    const pressed = get('entry-list').children.filter(button=>button.getAttribute('aria-pressed')==='true');
    same(pressed.map(button=>button.dataset.entry), [id], 'One catalog entry is pressed');
    if (chart) same(chart.nodes('.inspected').map(node=>node.id()), [id], 'Real headless Cytoscape marks the same node');
  }
  return {get, change, expectEntry, downloads, clipboardCopies, document, chart:()=>chart};
}
try {
  const f = fixture();
  const selectionCommand = 'node scripts/check_atlas_selection.cjs';
  const displayedCommands = f.get('reproduce-commands').textContent;
  same(displayedCommands.split('\n').filter(line=>line.trim()===selectionCommand).length,1,'Runtime reproduction list includes the selection checker exactly once');
  const staticCommands = /<pre id="reproduce-commands">([\s\S]*?)<\/pre>/.exec(html)?.[1] || '';
  same(staticCommands.split('\n').filter(line=>line.trim()===selectionCommand).length,1,'Static reproduction list includes the selection checker exactly once');
  f.get('copy-commands').click();
  same(f.clipboardCopies,[displayedCommands],'Copy commands passes the complete displayed runtime list to the clipboard API');
  const editedCommands = `${displayedCommands}\n# local annotation`;
  f.get('reproduce-commands').textContent = editedCommands;
  f.get('copy-commands').click();
  same(f.clipboardCopies[1],editedCommands,'Copy commands reads current displayed text rather than a cached list');
  f.get('reproduce-commands').textContent = displayedCommands;
  // This assertion fails on the exact unmodified base: map defaults to C4, detail to B2.
  f.expectEntry('n4-E16403');
  f.get('map-entry').focus();
  f.change('map-entry','n4-E16457'); f.expectEntry('n4-E16457');
  same(f.document.activeElement, f.get('map-entry'), 'Passive selection does not steal focus');
  f.get('map-open-entry').click(); same(f.document.activeElement,f.get('entry-title'),'Explicit jump focuses detail heading');
  f.get('comparison-cards').children.find(button=>button.dataset.compare==='n4-E16403').click(); f.expectEntry('n4-E16403');
  f.chart().getElementById('n4-E16457').emit('tap'); f.expectEntry('n4-E16457');
  const catalogButton = f.get('entry-list').children.find(button=>button.dataset.entry==='n4-E16403');
  catalogButton.focus(); catalogButton.click(); f.expectEntry('n4-E16403');
  same(f.document.activeElement,catalogButton,'Catalog selection preserves the focused button');
  f.get('download-entry').click();
  same(f.downloads[0].name,'atlas-n4-E16403.json','Download name follows shared selection');
  const exported = JSON.parse(f.downloads[0].text);
  same(exported.entry.id,'n4-E16403','Downloaded exact entry');
  same(exported.claims.records.filter(record=>record.entry_id==='n4-E16403').map(record=>record.id),['construction:n4-E16403','minimum:n4-E16403'],'Export contains full exact claim records');
  same(exported.claims.registry_git_revision,null,'No invented registry Git revision');
  f.change('map-carrier','1');
  ok(f.document.detail.hidden,'No-match filter hides stale detail');
  ok(f.get('download-entry').disabled && f.get('map-entry').disabled && f.get('map-open-entry').disabled,'No-match controls disabled');
  same(f.get('entry-json').textContent,'','No stale certificate remains');
  same(f.get('entry-claims').innerHTML,'','No stale claims remain');
  f.change('shape-filter','all');
  const zero = data.entries.find(entry=>entry.carrier_size===1);
  f.expectEntry(zero.id); ok(f.get('entry-claims').innerHTML.includes('Minimum unary operations</dt><dd>0</dd>'),'Zero is not missing');
  f.change('carrier-filter','all');
  const shapeNode = f.chart().nodes('[kind="shape"]').find(node=>node.data('abstract_type')==='T06');
  shapeNode.emit('tap'); f.expectEntry('n4-E16403');
  f.get('map-reset').click(); f.expectEntry('n4-E16403');
  fixture('?entry=n4-E16457').expectEntry('n4-E16457');
  fixture('?entry=not-an-entry').expectEntry('n4-E16403');
  for (const renderer of ['absent','throws']) {
    const fallback = fixture('',renderer); fallback.change('map-entry','n4-E16457'); fallback.expectEntry('n4-E16457');
    ok(!fallback.get('map-fallback').hidden,'Native fallback remains available');
    ok(fallback.get('construction-map').hidden,'Unavailable canvas hidden');
  }
  for (const entry of data.entries) {
    const selected = app.createSelection(data,entry.id); same(selected.snapshot().entry.id,entry.id,'Every entry can be addressed exactly');
    const exact = app.claimsForEntry(registry,entry).filter(claim=>claim.entry_id===entry.id);
    for (const claim of exact) {
      const gates=app.evidenceGates(claim); same(gates.filter(([gate,status])=>['Lean compilation','Kernel replay','Allowed-axiom audit','Formal theorem/data binding','Model performance'].includes(gate)).every(([,status])=>status==='Not supplied for this claim'),true,'Absent formal gates stay unknown');
    }
  }
  const model=app.createSelection(data);
  const before=model.snapshot();
  for (const action of [()=>model.select('bad'),()=>model.setFilters('5','all'),()=>model.setFilters('all','N5-proof')]) assert.throws(action);
  same(model.snapshot(),before,'Invalid identifiers cannot mutate selection');
  const escapedRegistry={...registry,claims:registry.claims.map(claim=>claim.id==='construction:n4-E16403'?{...claim,statement:'<script>alert("claim")</script>',assumptions:['<img onerror=alert(1)>']}:claim)};
  const escaped=app.claimsHtml(escapedRegistry,data.entries.find(entry=>entry.id==='n4-E16403'));
  ok(!escaped.includes('<script>')&&!escaped.includes('<img onerror'),'Claim text is escaped');
  const css=read('space/atlas-research.css');
  const tokens=Object.fromEntries([...css.split('}')[0].matchAll(/(--[\w-]+):\s*(#[0-9a-f]{6})/g)].map(m=>[m[1],m[2]]));
  const luminance=hex=>hex.slice(1).match(/../g).map(s=>parseInt(s,16)/255).map(c=>c<=.04045?c/12.92:((c+.055)/1.055)**2.4).reduce((sum,c,i)=>sum+c*[.2126,.7152,.0722][i],0);
  const contrast=(a,b)=>{const x=luminance(a),y=luminance(b);return (Math.max(x,y)+.05)/(Math.min(x,y)+.05);};
  let minText=Infinity,minBoundary=Infinity;
  for (const surface of ['--paper','--ground','--surface-soft','--wash']) for(const text of ['--ink','--body','--muted','--accent','--teal']) {
    const ratio=contrast(tokens[text],tokens[surface]); minText=Math.min(minText,ratio);ok(ratio>=4.5,`${text} on ${surface}`);
  }
  for (const fill of ['--graph-construction','--graph-shape']) ok(contrast('#ffffff',tokens[fill])>=4.5,'Canvas label contrast');
  for (const token of ['--control-border','--graph-edge','--graph-selected']) for (const surface of ['--ground','--paper','--surface-soft']) {
    const ratio=contrast(tokens[token],tokens[surface]);minBoundary=Math.min(minBoundary,ratio);ok(ratio>=3,`${token} boundary contrast`);
  }
  ok(html.includes('aria-label="Exact selected claim inspector"'),'Named claim region');
  ok(css.includes('@media(forced-colors:active)'),'System-color fallback');
  ok(css.includes('min-height:44px'),'Declared native control target size');
  ok(css.includes(':focus-visible'),'Visible focus source rules');
  ok(read('space/atlas.css').includes('prefers-reduced-motion:reduce'),'Reduced-motion source rule');
  const claimsHtml=app.claimsHtml(registry,data.entries[0]);
  ok(claimsHtml.includes('<caption>')&&claimsHtml.includes('scope="col"')&&claimsHtml.includes('scope="row"'),'Evidence table semantics');
  checkAtlasContrast(root);
  console.log(`Selection/inspector checks passed: ${checks} assertions; real headless Cytoscape + explicit DOM fixture; 39 exact entry IDs; native fallback and renderer-error paths; text contrast >= ${minText.toFixed(2)}:1, boundary contrast >= ${minBoundary.toFixed(2)}:1. Browser layout, assistive technology and canvas rendering NOT tested.`);
} finally { charts.forEach(chart=>chart.destroy()); }
