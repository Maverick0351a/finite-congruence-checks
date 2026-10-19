/* Check the saved TM comparison view without executing the machines in JS. */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const root = path.resolve(__dirname, '..');
const app = require('../space/tm-atlas.js');
const data = JSON.parse(fs.readFileSync(path.join(root, 'space/tm-atlas-data.json'), 'utf8'));
const wrapperContext = { window: {} };
vm.runInNewContext(fs.readFileSync(path.join(root, 'space/tm-atlas-data.js'), 'utf8'), wrapperContext);
assert.deepEqual(JSON.parse(JSON.stringify(wrapperContext.window.TM_ATLAS_DATA)), data, 'Offline JS and JSON must agree.');
assert.deepEqual(data, JSON.parse(fs.readFileSync(path.join(root, 'evidence/tm-atlas-v1.json'), 'utf8')), 'UI data must match the retained pair evidence.');
assert(app.validData(data), 'Complete pair data should pass the view consistency check.');
const expectedVerdicts = {
  'tm-pair:tiny-stay:v1': [true, false, true],
  'tm-pair:bb2:v1': [true, true, false],
  'tm-pair:bb3:v1': [true, true, false],
  'tm-pair:bb4:v1': [true, false, false],
};
assert.deepEqual(data.pairs.map(pair => pair.id).sort(), Object.keys(expectedVerdicts).sort());
let configurations = 0, citations = 0;
for (const pair of data.pairs) {
  const claims = app.claimsForPair(data, pair), observations = app.observations(pair);
  assert.equal(claims.length, 3);
  assert.deepEqual(app.PROPERTIES.map(([property]) => observations[property].equal), expectedVerdicts[pair.id]);
  const propertyHtml = app.comparisonHtml(pair, claims);
  for (const [index, [property, title]] of app.PROPERTIES.entries()) {
    const claim = claims[index];
    assert.equal(claim.property, property);
    assert(propertyHtml.includes(`<h4>${title}</h4>`));
    assert(propertyHtml.includes(`href="#${app.claimAnchor(claim)}"`));
  }
  assert.equal((propertyHtml.match(/class="tm-verdict(?: differs)?"/g) || []).length, 3);
  assert(!propertyHtml.includes('State'), 'Numeric state equality must not become a comparison verdict.');
  const bounds = app.tapeBounds(pair), tapeHtml = app.finalTapesHtml(pair);
  const width = bounds[1] - bounds[0] + 1;
  assert.equal((tapeHtml.match(/data-position=/g) || []).length, 2 * width);
  for (const side of ['left', 'right']) {
    const item = pair[side], finalHtml = app.tapeHtml(pair, side, bounds);
    const cells = [...finalHtml.matchAll(/class="tm-cell([^"]*)" data-position="(-?\d+)" data-symbol="(\d+)"/g)].map(match => ({ classes: match[1], position: Number(match[2]), symbol: Number(match[3]) }));
    assert.deepEqual(cells.filter(cell => cell.symbol).map(cell => [cell.position, cell.symbol]), item.final.tape, 'Every nonzero final cell is drawn at its exact integer coordinate.');
    assert.deepEqual(cells.filter(cell => cell.classes.includes('is-head')).map(cell => cell.position), [item.final.head], 'Exactly one head arrow, including when its cell is zero.');
    assert(cells.some(cell => cell.symbol === 0), 'Zero cells must remain visible.');
    assert.equal(cells[0].position, bounds[0]);
    assert.equal(cells.at(-1).position, bounds[1]);
    assert(/tabindex="0" role="region" aria-label=/.test(finalHtml), 'Tape overflow must support keyboard scrolling.');
    assert(finalHtml.includes(`href="#${app.traceAnchor(pair, side, item.first_halt)}"`));
    const traceHtml = app.traceHtml(pair, side);
    assert(traceHtml.includes('State numbers are internal labels'));
    assert(traceHtml.includes(app.escapeHtml(item.case_id)));
    for (const [index, record] of item.trace.entries()) {
      assert.equal(record.steps, index);
      assert(traceHtml.includes(`id="${app.traceAnchor(pair, side, record.steps)}"`));
      assert(traceHtml.includes(app.escapeHtml(JSON.stringify(record, null, 2))), 'Each row exposes the exact saved record.');
      assert(traceHtml.includes(app.escapeHtml(item.trace_sources[index].sha256)));
      assert.equal(app.sourceHref(item.trace_sources[index]), item.trace_sources[index].url);
      assert(traceHtml.includes(app.escapeHtml(item.trace_sources[index].url)), 'Native trace lines use their pinned commit.');
      assert(traceHtml.includes(app.escapeHtml(item.trace_sources[index].input_source.url)), 'Native input lines use their pinned commit.');
      configurations++;
    }
    assert.equal(item.trace.find(record => record.halted).steps, item.first_halt);
  }
  const claimHtml = app.claimsHtml(pair, claims), lemmaHtml = app.lemmasHtml(pair, claims);
  for (const claim of claims) {
    assert(claimHtml.includes(`id="${app.claimAnchor(claim)}"`));
    for (const sentence of [claim.statement, claim.scope, ...(claim.assumptions || []), ...(claim.limits || [])]) if (sentence) assert(claimHtml.includes(app.escapeHtml(sentence)));
    for (const citation of claim.citations) {
      assert(claimHtml.includes(app.escapeHtml(citation.path)));
      assert(claimHtml.includes(app.escapeHtml(citation.sha256)));
      if (citation.json_pointer) assert(claimHtml.includes(app.escapeHtml(citation.json_pointer)));
      citations++;
    }
    for (const lemma of claim.applicable_lemmas) {
      assert(lemmaHtml.includes(`id="${app.lemmaAnchor(pair, lemma)}"`));
      assert(lemmaHtml.includes(app.escapeHtml(lemma.theorem)));
      assert(lemmaHtml.includes(app.escapeHtml(lemma.applicability)));
      for (const condition of lemma.conditions) assert(lemmaHtml.includes(app.escapeHtml(condition)));
      assert.equal(app.sourceHref(lemma.source), lemma.source.url);
      assert(lemmaHtml.includes(app.escapeHtml(lemma.source.url)));
      assert(lemmaHtml.includes(app.escapeHtml(lemma.case_id)));
      assert(lemmaHtml.includes(app.escapeHtml(lemma.evidence_boundary)));
      for (const step of Object.values(lemma.at_steps)) assert(lemmaHtml.includes(`href="#${app.traceAnchor(pair, lemma.side, step)}"`));
    }
  }
  const rendered = propertyHtml + tapeHtml + claimHtml + lemmaHtml + ['left', 'right'].map(side => app.traceHtml(pair, side)).join('');
  const generatedIds = [...rendered.matchAll(/\bid="([^"]+)"/g)].map(match => match[1]);
  assert.equal(new Set(generatedIds).size, generatedIds.length, 'Every generated trace/claim/lemma anchor is unique.');
  for (const [, anchor] of rendered.matchAll(/href="#(tm-[^"]+)"/g)) assert(generatedIds.includes(anchor), 'Every in-panel citation opens a real HTML target.');
  assert(!/href="[^"\n]+\.json#\//.test(rendered), 'JSON pointers are evidence locations, not fake browser anchors.');
  const fixedApplications = claims.flatMap(claim => claim.applicable_lemmas).filter(lemma => lemma.theorem.endsWith('.halted_fixed'));
  assert.equal(new Set(fixedApplications.map(lemma => app.lemmaAnchor(pair, lemma))).size, 2, 'The two halted_fixed applications keep separate side/step anchors.');
}

assert.equal(app.escapeHtml('<script>"&\''), '&lt;script&gt;&quot;&amp;&#39;');
assert.equal(app.sourceUrl('../outside'), null);
const pinnedSource = data.pairs[0].left.trace_sources[0];
for (const url of ['javascript:alert(1)', pinnedSource.url.replace('github.com', 'example.com'), pinnedSource.url.replace('/lean.jsonl', '/other.jsonl'), pinnedSource.url + '" onclick="alert(1)']) {
  assert.equal(app.sourceHref({ ...pinnedSource, url }), null, 'Untrusted URLs must match the exact repository, commit, path, and lines.');
}
assert.equal(app.sourceHref({ ...pinnedSource, source_commit: 'main' }), null);
assert.equal(app.validData(null), false);
assert.equal(app.validData({ schema_version: 1, pairs: [] }), false);
const corrupted = structuredClone(data);
corrupted.claims[0].observation.equal = !corrupted.claims[0].observation.equal;
assert.equal(app.validData(corrupted), false, 'Inconsistent displayed claims must fail closed.');
const missingTrace = structuredClone(data);
missingTrace.pairs[0].left.trace.pop();
assert.equal(app.validData(missingTrace), false, 'Incomplete traces must fail closed.');
const missingSource = structuredClone(data);
missingSource.pairs[0].left.trace_sources[0] = null;
assert.equal(app.validData(missingSource), false, 'Incomplete source locators must fail closed before rendering.');
const missingApplication = structuredClone(data);
delete missingApplication.claims[0].applicable_lemmas[0].at_steps;
assert.equal(app.validData(missingApplication), false, 'Incomplete lemma applications must fail closed before rendering.');
const escapedPair = structuredClone(data.pairs[0]);
escapedPair.left.label = '<img src=x onerror=alert(1)>';
assert(!app.tapeHtml(escapedPair, 'left').includes('<img'), 'Labels must never introduce markup.');

const html = fs.readFileSync(path.join(root, 'space/atlas.html'), 'utf8');
const js = fs.readFileSync(path.join(root, 'space/tm-atlas.js'), 'utf8');
const ids = [...html.matchAll(/\bid="([^"]+)"/g)].map(match => match[1]);
assert.equal(new Set(ids).size, ids.length);
assert(ids.includes('turing'));
assert(html.includes('for="tm-pair-select"'));
assert(/<select id="tm-pair-select"[^>]*aria-describedby="tm-scope"/.test(html));
assert(html.includes('src="tm-atlas-data.js" defer'));
assert(html.includes('src="tm-atlas.js" defer'));
assert(html.indexOf('src="tm-atlas-data.js"') < html.indexOf('src="tm-atlas.js"'));
assert(!/<script[^>]+src="https?:/.test(html), 'Offline view uses local scripts.');
for (const [, id] of js.matchAll(/byId\('([^']+)'\)/g)) assert(ids.includes(id), `Missing HTML target: ${id}`);

// Minimal DOM checks exercise native selector events, safe fallback, and deep links.
function boot(payload) {
  const elements = new Map(ids.map(id => [id, { id, innerHTML: '', textContent: '', hidden: id === 'tm-app', value: '', listeners: {}, addEventListener(type, fn) { this.listeners[type] = fn; } }]));
  const events = {}, window = { TM_ATLAS_DATA: payload, location: { hash: '' }, addEventListener(type, fn) { events[type] = fn; } };
  window.history = { state: { retained: true }, replacements: [], replaceState(state, title, hash) { this.replacements.push({ state, title, hash }); window.location.hash = hash; } };
  const context = { window, document: { getElementById: id => elements.get(id) || null } };
  vm.runInNewContext(js, context);
  return { elements, events, window };
}
const absent = boot(undefined);
assert(absent.elements.get('tm-app').hidden);
assert(absent.elements.get('tm-loading').innerHTML.includes('unavailable'));
const invalid = boot(corrupted);
assert(invalid.elements.get('tm-app').hidden);
const live = boot(data), selector = live.elements.get('tm-pair-select');
assert(!live.elements.get('tm-app').hidden);
for (const pair of data.pairs) {
  selector.value = pair.id;
  selector.listeners.change();
  assert.equal(live.elements.get('tm-pair-title').textContent, pair.name);
  assert.equal(live.elements.get('tm-summary').textContent, app.summaryText(pair));
}
const pair = data.pairs[0], anchor = app.traceAnchor(pair, 'left', pair.left.first_halt);
const details = { tagName: 'DETAILS', open: false, parentElement: null };
const target = { parentElement: details, scrolled: false, focused: false, scrollIntoView() { this.scrolled = true; }, focus() { this.focused = true; } };
live.elements.set(anchor, target);
live.window.location.hash = '#' + anchor;
live.events.hashchange();
assert.equal(selector.value, pair.id, 'A trace permalink selects its pair.');
assert(details.open && target.scrolled && target.focused, 'A trace permalink opens the viewer and focuses the exact row.');
assert.equal(live.window.location.hash, '#' + anchor, 'Deep-link navigation preserves the exact evidence fragment.');
assert.equal(live.window.history.replacements.length, 0, 'Deep-link navigation does not replace browser history.');
for (const staleAnchor of [anchor, app.claimAnchor(app.claimsForPair(data, pair)[0]), app.lemmaAnchor(pair, app.claimsForPair(data, pair)[0].applicable_lemmas[0])]) {
  live.window.location.hash = '#' + staleAnchor;
  target.scrolled = false;
  selector.value = data.pairs[3].id;
  selector.listeners.change();
  assert.equal(live.window.location.hash, '#turing', 'Explicit pair selection clears a stale evidence fragment.');
  assert.equal(live.elements.get('tm-pair-title').textContent, data.pairs[3].name);
  assert.equal(target.scrolled, false, 'Replacing a stale fragment does not scroll back to the old evidence.');
  assert.deepEqual(live.window.history.replacements.at(-1), { state: live.window.history.state, title: '', hash: '#turing' });
}
live.window.location.hash = '#atlas';
selector.listeners.change();
assert.equal(live.window.location.hash, '#atlas', 'Pair selection preserves unrelated page fragments.');
assert.equal(JSON.parse(fs.readFileSync(path.join(root, 'space/atlas-data.json'), 'utf8')).entries.length, 39, 'The congruence census remains separate.');
console.log(`TM atlas UI checks passed: 4 pairs, 12 separate property claims, ${configurations} exact trace rows, ${citations} source citations; selector, deep links, escaping, and missing/inconsistent data fallbacks checked.`);
