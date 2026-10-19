/* Exercise the actual Snaky renderer against every saved state, without Lean. */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const root = path.resolve(__dirname, '..');
const app = require('../space/snaky-play.js');
const read = relative => fs.readFileSync(path.join(root, relative), 'utf8');
const json = relative => JSON.parse(read(relative));
const plain = value => JSON.parse(JSON.stringify(value));
const sorted = cells => cells.map(p => p.join(',')).sort();
assert(process.argv.slice(2).every(arg => arg === '--example-only'), 'Unknown command option');
const exampleOnly = process.argv.includes('--example-only');
const play = json('evidence/snaky-play-v1/example.json');
let data;
if (exampleOnly) {
  // Explicit development mode: this checks real saved states, with no proof claim.
  data = {schema_version: 1, play, evidence: [], commands: []};
} else {
  // No fallback: CI must fail if publication prerequisites have not been created.
  data = json('space/snaky-play.json');
  const context = {window: {}};
  vm.runInNewContext(read('space/snaky-play-data.js'), context);
  assert.deepEqual(plain(context.window.SNAKY_PLAY_DATA), data, 'Offline JS and download JSON must agree');
  assert.deepEqual(data.play, play, 'The displayed play must match the independently checked record');
  const anchor = json('specs/snaky-play-source-anchor.json');
  assert.match(data.source_revision, /^[0-9a-f]{40}$/);
  assert.equal(data.source_revision, anchor.revision);
  assert.equal(data.claim_record.claim.id, play.sources.root_claim_id);
  assert.deepEqual(data.claim_record.claim.values.envelope, play.board.cells);
  assert.equal(data.claim_record.claim.conclusion.maker_claims_at_most, 21);
  assert.equal(data.evidence.length, 3);
  for (const item of data.evidence) {
    assert.equal(item.url, `https://github.com/Maverick0351a/finite-congruence-checks/blob/${anchor.revision}/${item.path}`);
    assert.equal(item.sha256, anchor.files[item.path]);
    assert.match(item.sha256, /^[0-9a-f]{64}$/);
  }
}

assert.equal(play.steps.length, 8);
assert.equal(play.board.cells.length, 251);
const finalCells = [[8,7],[8,8],[8,9],[8,10],[9,10],[9,11]];
assert.deepEqual(play.result.target.cells, finalCells);
assert.deepEqual(play.steps.map(s => s.active.height), [21,20,18,14,7,3,2,1]);
assert.equal(play.result.remaining_global_budget, 13);
for (const invalid of [-1, 8, 0.5, NaN, '1', null]) {
  assert.throws(() => app.viewOf(data, invalid), /Unknown move/);
}

const html = read('space/snaky-play.html');
const js = read('space/snaky-play.js');
const ids = [...html.matchAll(/\bid="([^"]+)"/g)].map(m => m[1]);
assert.equal(new Set(ids).size, ids.length, 'HTML IDs must be unique');
for (const [, id] of js.matchAll(/el\("([^"]+)"\)/g)) assert(ids.includes(id), `Missing renderer target ${id}`);
assert(html.includes('for="snaky-step"'));
assert(/<select id="snaky-step"/.test(html), 'Move selection uses a native keyboard control');
for (const id of ['snaky-prev', 'snaky-next']) assert(new RegExp(`<button[^>]*id="${id}"[^>]*aria-label=`).test(html));
assert(html.includes('aria-live="polite"'));
assert(html.includes('href="snaky-play.json" download'));
assert(html.indexOf('src="snaky-play-data.js"') < html.indexOf('src="snaky-play.js"'));
assert(/src="snaky-play-data.js" defer/.test(html) && /src="snaky-play.js" defer/.test(html));
assert(!/<script[^>]+src="https?:/.test(html), 'The offline viewer must not depend on remote scripts');
assert(html.includes('not a formally verified extraction'));
assert(html.includes('does not establish a better move bound'));

class Element {
  constructor(tag, id = null) { this.tagName = tag.toUpperCase(); this.id = id; this.children = []; this.attrs = {}; this.listeners = {}; this.hidden = false; this.value = ''; this.disabled = false; this._text = ''; }
  set textContent(value) { this._text = String(value); this.children = []; }
  get textContent() { return this._text + this.children.map(c => c.textContent).join(''); }
  append(...children) { this.children.push(...children); }
  replaceChildren(...children) { this._text = ''; this.children = children; }
  setAttribute(key, value) { this.attrs[key] = String(value); }
  addEventListener(event, handler) { this.listeners[event] = handler; }
}
function descendants(element, predicate) {
  return [...(predicate(element) ? [element] : []), ...element.children.flatMap(c => descendants(c, predicate))];
}
function boot(payload) {
  const elements = new Map(ids.map(id => [id, new Element('div', id)]));
  elements.get('snaky-content').hidden = true;
  elements.get('snaky-error').hidden = true;
  const document = {getElementById: id => elements.get(id), createElement: tag => new Element(tag), createElementNS: (_ns, tag) => new Element(tag)};
  vm.runInNewContext(js, {window: {SNAKY_PLAY_DATA: payload}, document});
  return elements;
}
for (const absent of [undefined, null, {schema_version: 2}]) {
  const failed = boot(absent);
  assert(failed.get('snaky-content').hidden);
  assert(!failed.get('snaky-error').hidden);
  assert(failed.get('snaky-error').textContent.includes('could not be loaded'));
}
const live = boot(data);
assert(!live.get('snaky-content').hidden, live.get('snaky-error').textContent);
assert(live.get('snaky-error').hidden);
const select = live.get('snaky-step');
assert.equal(select.children.length, 8);
assert.equal(descendants(live.get('snaky-move-table'), n => n.tagName === 'TBODY')[0].children.length, 8);
const board = new Set(sorted(play.board.cells));

for (let index = 0; index < 8; index++) {
  select.value = String(index);
  select.listeners.change();
  const step = play.steps[index], view = app.viewOf(data, index);
  assert.equal(view.step, step);
  assert.deepEqual([...view.makerTurns.keys()].sort(), sorted(step.maker_after));
  assert.deepEqual([...view.breakerTurns.keys()].sort(), sorted(step.breaker_after));
  assert.equal(view.makerTurns.size, index + 1);
  assert.equal(view.breakerTurns.size, Math.min(index + 1, 7));
  assert.deepEqual(view.envelope, index < 7 ? play.steps[index + 1].active.envelope : [], 'Outline is the surviving next envelope after this reply');
  assert.deepEqual(view.winner, index === 7 ? finalCells : []);
  assert.equal(live.get('snaky-prev').disabled, index === 0);
  assert.equal(live.get('snaky-next').disabled, index === 7);
  assert.equal(live.get('snaky-card-source').href, step.active.certificate_ref.url);
  const budget = live.get('snaky-budget').children.filter(n => n.tagName === 'DD').map(n => n.textContent);
  assert.deepEqual(budget, [String(index+1), String(20-index), String(step.active.height), index === 7 ? 'Won' : String(step.continuation.height)]);
  const svg = live.get('snaky-board').children[0];
  assert.equal(svg.attrs.role, 'img');
  assert.equal(svg.attrs['aria-labelledby'], 'snaky-board-title snaky-board-desc');
  const rects = descendants(svg, n => n.tagName === 'RECT');
  assert.equal(rects.length, 289);
  const coordinate = rect => [(Number(rect.attrs.x)-28)/25, 16-(Number(rect.attrs.y)-12)/25];
  const drawn = klass => sorted(rects.filter(r => (r.attrs.class || '').split(' ').includes(klass)).map(coordinate));
  assert.deepEqual(drawn('on-board'), [...board].sort());
  assert.deepEqual(drawn('in-envelope'), sorted(view.envelope));
  assert.deepEqual(drawn('winning'), sorted(view.winner));
  for (const rect of rects) {
    const key = coordinate(rect).join(',');
    const expected = view.makerTurns.has(key) ? `Maker, move ${view.makerTurns.get(key)}` : view.breakerTurns.has(key) ? `Breaker, reply ${view.breakerTurns.get(key)}` : board.has(key) ? 'free' : 'outside board';
    assert(rect.children[0].textContent.endsWith(': ' + expected));
  }
  const circles = descendants(svg, n => n.tagName === 'CIRCLE');
  assert.deepEqual(sorted(circles.map(n => [(Number(n.attrs.cx)-36)/25, 16-(Number(n.attrs.cy)-21)/25])), sorted(step.maker_after));
  const crosses = descendants(svg, n => n.tagName === 'PATH');
  assert.deepEqual(sorted(crosses.map(n => { const match = /^M([\d.]+),([\d.]+)/.exec(n.attrs.d); return [(Number(match[1])-32)/25, 16-(Number(match[2])-16)/25]; })), sorted(step.breaker_after));
  if (index < 7) {
    assert(view.envelope.every(p => !view.breakerTurns.has(p.join(','))));
    assert(play.steps[index+1].active.required.every(p => view.makerTurns.has(p.join(','))));
    live.get('snaky-next').listeners.click();
    assert.equal(select.value, String(index+1));
    live.get('snaky-prev').listeners.click();
    assert.equal(select.value, String(index));
  } else {
    assert.equal(view.winner.length, 6);
    assert(view.winner.every(p => view.makerTurns.has(p.join(','))));
    for (const point of finalCells) assert(live.get('snaky-continuation').textContent.includes(app.pointText(point)));
    assert(live.get('snaky-move-text').textContent.includes('no Breaker reply'));
  }
}
assert.deepEqual(descendants(live.get('snaky-evidence'), n => n.tagName === 'A').map(n => n.href), data.evidence.map(e => e.url));
assert.equal(live.get('snaky-query').textContent, data.commands.join('\n'));
console.log(`PASS: 8 rendered ownership states, next-envelope outlines, 6 winning cells, selector/buttons, exact card links, and unavailable-data fallback. ${exampleOnly ? 'EXAMPLE-ONLY: proof receipt, publication anchor, and generated packet were not tested.' : 'Published JSON, JS wrapper, claim, and evidence anchor agree.'}`);
