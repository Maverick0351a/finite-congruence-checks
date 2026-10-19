/* Display saved bounded TM comparisons; no machine simulation runs in the browser. */
(function () {
  'use strict';
  const REPOSITORY = 'https://github.com/Maverick0351a/finite-congruence-checks/blob/';
  const PROPERTIES = Object.freeze([
    ['halting_time', 'First halting step'],
    ['tape', 'Complete final tape'],
    ['head_position', 'Final head position'],
  ]);
  const escapeHtml = value => String(value).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
  const slug = value => String(value).replace(/[^a-zA-Z0-9_-]/g, '-');
  const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
  const nat = value => Number.isSafeInteger(value) && value >= 0;
  const number = value => escapeHtml(value < 0 ? `−${-value}` : value);
  const claimAnchor = claim => `tm-claim-${slug(claim.id)}`;
  const traceAnchor = (pair, side, step) => `tm-trace-${slug(pair.id)}-${side}-step-${step}`;
  const lemmaAnchor = (pair, lemma) => `tm-lemma-${slug(pair.id)}-${slug(lemma.lemma_id)}-${lemma.side}-${lemma.at_steps.before}-${lemma.at_steps.after}`;

  function sourceUrl(path, line, lastLine, commit = 'main') {
    if (typeof path !== 'string' || !path || path.split('/').some(part => !part || part === '..' || part === '.')) return null;
    if (commit !== 'main' && !/^[a-f0-9]{40}$/.test(commit)) return null;
    const url = REPOSITORY + commit + '/' + path.split('/').map(encodeURIComponent).join('/');
    return /\.(lean|py|md|js|jsonl|toml)$/.test(path) && nat(line) && line > 0
      ? url + `#L${line}${nat(lastLine) && lastLine > line ? `-L${lastLine}` : ''}` : url;
  }
  function sourceHref(source) {
    if (!source || typeof source !== 'object') return null;
    const expected = sourceUrl(source.path, source.line, source.last_line, source.source_commit || 'main');
    if (source.url !== undefined && (!/^[a-f0-9]{40}$/.test(source.source_commit || '') || source.url !== expected)) return null;
    return expected;
  }
  function sourceLink(source, label) {
    const href = sourceHref(source);
    return href ? `<a href="${escapeHtml(href)}">${escapeHtml(label || source.path)} ↗</a>` : escapeHtml(label || source.path || 'Source record');
  }
  function citationHtml(citation) {
    return `<li>${sourceLink(citation)}${citation.json_pointer ? `<br><code>JSON pointer: ${escapeHtml(citation.json_pointer)}</code>` : ''}${citation.line ? `<br><code>Source line ${escapeHtml(citation.line)}${citation.last_line ? `–${escapeHtml(citation.last_line)}` : ''}</code>` : ''}${citation.sha256 ? `<small>SHA-256: <code>${escapeHtml(citation.sha256)}</code></small>` : ''}</li>`;
  }
  function observations(pair) {
    const a = pair.left, b = pair.right;
    return {
      halting_time: { left: a.first_halt, right: b.first_halt, equal: a.first_halt === b.first_halt },
      tape: { left: a.final.tape, right: b.final.tape, equal: same(a.final.tape, b.final.tape) },
      head_position: { left: a.final.head, right: b.final.head, equal: a.final.head === b.final.head },
    };
  }
  function claimsForPair(data, pair) {
    return PROPERTIES.map(([property]) => data.claims.find(claim => claim.pair_id === pair.id && claim.property === property));
  }
  function validRecord(record) {
    if (!record || !nat(record.steps) || !nat(record.state) || !Number.isSafeInteger(record.head) || typeof record.halted !== 'boolean' || !Array.isArray(record.tape)) return false;
    return record.tape.every((cell, i) => Array.isArray(cell) && cell.length === 2 && Number.isSafeInteger(cell[0]) && nat(cell[1]) && cell[1] > 0 && (i === 0 || record.tape[i - 1][0] < cell[0]));
  }
  function validSource(source) {
    return !!source && !!sourceHref(source) && /^[a-f0-9]{64}$/.test(source.sha256 || '')
      && (source.line === undefined || (nat(source.line) && source.line > 0))
      && (source.input_source === undefined || validSource(source.input_source));
  }
  function validData(data) {
    if (!data || data.schema_version !== 1 || data.namespace !== 'finite-congruence-atlas/tm-pairs-v1' || !Array.isArray(data.pairs) || data.pairs.length !== 4 || !Array.isArray(data.claims) || data.claims.length !== 12) return false;
    const ids = data.pairs.map(pair => pair && pair.id);
    if (new Set(ids).size !== 4 || ids.some(id => typeof id !== 'string')) return false;
    try {
      if (!data.sources || !Object.values(data.sources).every(validSource)) return false;
      if (new Set(data.claims.map(claim => claim.id)).size !== 12) return false;
      return data.pairs.every(pair => {
        if (typeof pair.name !== 'string' || !Array.isArray(pair.input) || pair.input.length) return false;
        for (const side of ['left', 'right']) {
          const item = pair[side];
          if (!item || typeof item.label !== 'string' || !nat(item.first_halt) || !validRecord(item.final) || !item.final.halted || item.final.steps !== item.first_halt || !Array.isArray(item.trace) || item.trace.length !== item.first_halt + 2 || !Array.isArray(item.trace_sources) || item.trace_sources.length !== item.trace.length) return false;
          if (!item.trace.every((record, i) => validRecord(record) && record.steps === i && record.halted === (i >= item.first_halt))) return false;
          if (!item.trace_sources.every(validSource)) return false;
          if (!same(item.final, item.trace[item.first_halt])) return false;
        }
        const expected = observations(pair), claims = claimsForPair(data, pair);
        return claims.every(claim => {
          if (!claim || typeof claim.id !== 'string' || typeof claim.statement !== 'string' || !Array.isArray(claim.citations) || !Array.isArray(claim.applicable_lemmas)) return false;
          if (!claim.citations.every(validSource) || !claim.applicable_lemmas.every(lemma =>
            lemma && typeof lemma.lemma_id === 'string' && typeof lemma.theorem === 'string'
            && ['left', 'right'].includes(lemma.side) && lemma.case_id === pair[lemma.side].case_id
            && lemma.at_steps && nat(lemma.at_steps.before) && lemma.at_steps.after === lemma.at_steps.before + 1
            && lemma.at_steps.after < pair[lemma.side].trace.length && validSource(lemma.source)
            && Array.isArray(lemma.conditions) && lemma.conditions.every(condition => typeof condition === 'string')
            && typeof lemma.applicability === 'string' && Array.isArray(lemma.citations) && lemma.citations.every(validSource))) return false;
          const observed = claim.observation, wanted = expected[claim.property];
          return observed && observed.equal === wanted.equal && same(observed.left, wanted.left) && same(observed.right, wanted.right);
        });
      });
    } catch (_) { return false; }
  }
  function comparisonHtml(pair, claims) {
    const values = observations(pair);
    return PROPERTIES.map(([property, title], index) => {
      const value = values[property];
      const detail = property === 'halting_time'
        ? `Left: ${number(value.left)} steps · Right: ${number(value.right)} steps`
        : property === 'head_position'
          ? `Left: position ${number(value.left)} · Right: position ${number(value.right)}`
          : `Left: ${value.left.length} nonzero cells · Right: ${value.right.length} nonzero cells`;
      return `<section class="tm-property" aria-label="${title}"><h4>${title}</h4><strong class="tm-verdict${value.equal ? '' : ' differs'}">${value.equal ? 'Matches' : 'Differs'}</strong><p class="tm-values">${detail}</p>${property === 'tape' ? '<p>Symbols compared at every integer position, including zero cells.</p>' : ''}<a href="#${claimAnchor(claims[index])}">Inspect this claim ↓</a></section>`;
    }).join('');
  }
  function tapeBounds(pair) {
    const positions = [0, pair.left.final.head, pair.right.final.head, ...pair.left.final.tape.map(c => c[0]), ...pair.right.final.tape.map(c => c[0])];
    return [Math.min(...positions) - 1, Math.max(...positions) + 1];
  }
  function tapeHtml(pair, side, bounds = tapeBounds(pair)) {
    const item = pair[side], config = item.final, symbols = new Map(config.tape), [lower, upper] = bounds;
    const cells = [];
    for (let position = lower; position <= upper; position++) {
      const symbol = symbols.get(position) || 0, head = position === config.head;
      cells.push(`<span class="tm-cell${symbol ? ' is-nonzero' : ''}${head ? ' is-head' : ''}" data-position="${position}" data-symbol="${symbol}" role="img" aria-label="Cell ${position}: ${symbol}${head ? ', head here' : ''}"><span class="tm-head" aria-hidden="true">${head ? '↓' : ''}</span><b aria-hidden="true">${symbol}</b><small aria-hidden="true">${number(position)}</small></span>`);
    }
    return `<figure class="tm-tape"><figcaption>${escapeHtml(item.label)}</figcaption><p class="small">First halting step ${number(item.first_halt)} · head at ${number(config.head)}</p><div class="tm-tape-scroll" tabindex="0" role="region" aria-label="${escapeHtml(item.label)} final tape, positions ${lower} to ${upper}. Scroll horizontally with arrow keys."><div class="tm-tape-strip">${cells.join('')}</div></div><p class="caption"><a href="#${traceAnchor(pair, side, item.first_halt)}">Open this exact trace step ↓</a></p></figure>`;
  }
  function finalTapesHtml(pair) { const bounds = tapeBounds(pair); return ['left', 'right'].map(side => tapeHtml(pair, side, bounds)).join(''); }
  function traceLinks(pair) {
    return ['left', 'right'].map(side => `<a href="#${traceAnchor(pair, side, pair[side].first_halt)}">${escapeHtml(pair[side].label)} at step ${pair[side].first_halt}</a>`).join(' · ');
  }
  const listHtml = values => `<ul>${(Array.isArray(values) ? values : []).map(value => `<li>${escapeHtml(value)}</li>`).join('')}</ul>`;
  function claimsHtml(pair, claims) {
    return `<h4>Three claims, with separate evidence</h4>${claims.map((claim, index) => `<article id="${claimAnchor(claim)}" class="tm-claim" tabindex="-1"><h5>${PROPERTIES[index][1]}</h5><code>${escapeHtml(claim.id)}</code><p>${escapeHtml(claim.statement)}</p><p><strong>Scope:</strong> ${escapeHtml(claim.scope || 'Blank input; these exact encodings and saved traces.')}</p><p><strong>Evidence:</strong> ${escapeHtml(String(claim.evidence_status || '').replace(/_/g, ' '))}.</p><p>${traceLinks(pair)}</p><details class="tm-assumptions"><summary>Assumptions and limits</summary>${listHtml(claim.assumptions)}${listHtml(claim.limits)}</details><details><summary>Exact source citations and hashes</summary><ul class="tm-citations">${claim.citations.map(citationHtml).join('')}</ul></details>${claim.applicable_lemmas.length ? `<p class="caption">Applicable source lemmas: ${claim.applicable_lemmas.map(lemma => `<a href="#${lemmaAnchor(pair, lemma)}">${escapeHtml(lemma.theorem)}</a>`).join(', ')}. Read their conditions below.</p>` : ''}</article>`).join('')}`;
  }
  function supportText(tape) { return tape.length ? tape.map(([position, symbol]) => `${position}: ${symbol}`).join('; ') : 'empty (all cells zero)'; }
  function traceHtml(pair, side) {
    const item = pair[side];
    const rows = item.trace.map((record, i) => {
      const source = item.trace_sources[i], anchor = traceAnchor(pair, side, record.steps);
      return `<tr id="${anchor}" tabindex="-1"><td><a href="#${anchor}" aria-label="Link to ${escapeHtml(item.label)}, step ${record.steps}">${record.steps}</a></td><td>${record.state}</td><td>${number(record.head)}</td><td>${record.halted ? 'Yes' : 'No'}</td><td>${escapeHtml(supportText(record.tape))}<details><summary>Exact record &amp; source</summary><pre>${escapeHtml(JSON.stringify(record, null, 2))}</pre><ul class="tm-citations">${citationHtml(source)}${source.input_source ? citationHtml(source.input_source) : ''}</ul></details></td></tr>`;
    }).join('');
    return `<details class="tm-trace"><summary>${escapeHtml(item.label)} · ${item.trace.length} saved configurations</summary><p class="small">Includes step 0, every step through first halting, and one step after. State numbers are internal labels for this encoding.</p><p class="tm-trace-note">Case ID: <code>${escapeHtml(item.case_id)}</code>. Nonzero support lists <code>position: symbol</code>; every unlisted cell is zero.</p><div class="tm-trace-scroll" tabindex="0" role="region" aria-label="Scrollable complete trace for ${escapeHtml(item.label)}"><table><caption>Saved ${escapeHtml(item.label)} trace on blank input</caption><thead><tr><th scope="col">Step</th><th scope="col">State</th><th scope="col">Head</th><th scope="col">Halted?</th><th scope="col">Complete nonzero tape support</th></tr></thead><tbody>${rows}</tbody></table></div><details><summary>The exact encoded machine</summary><pre>${escapeHtml(JSON.stringify(item.machine, null, 2))}</pre></details></details>`;
  }
  function lemmasHtml(pair, claims) {
    const entries = new Map();
    for (const claim of claims) for (const lemma of claim.applicable_lemmas) {
      const key = lemmaAnchor(pair, lemma);
      if (!entries.has(key)) entries.set(key, { ...lemma, conditions: new Set(), applications: new Set(), citations: [] });
      const entry = entries.get(key);
      (lemma.conditions || []).forEach(condition => entry.conditions.add(condition));
      entry.applications.add(lemma.applicability);
      for (const citation of lemma.citations || []) if (!entry.citations.some(existing => same(existing, citation))) entry.citations.push(citation);
    }
    if (!entries.size) return '<h4>Source lemmas</h4><p>No applicable lemma records were supplied for this pair.</p>';
    return `<h4>Applicable source lemmas</h4><p class="small">These local general step lemmas use the pinned machine definitions. Each application below identifies its encoding, transition and conditions. The concrete pair comparisons remain saved execution evidence.</p>${[...entries.values()].map(lemma => `<article class="tm-lemma" id="${lemmaAnchor(pair, lemma)}" tabindex="-1"><h5>${escapeHtml(lemma.theorem)}</h5><code>${escapeHtml(lemma.lemma_id)}</code><p><strong>${escapeHtml(pair[lemma.side].label)}</strong> · <code>${escapeHtml(lemma.case_id)}</code><br>Transition: <a href="#${traceAnchor(pair, lemma.side, lemma.at_steps.before)}">step ${lemma.at_steps.before}</a> → <a href="#${traceAnchor(pair, lemma.side, lemma.at_steps.after)}">step ${lemma.at_steps.after}</a>.</p><p><strong>Conditions</strong></p>${listHtml([...lemma.conditions])}${[...lemma.applications].map(application => `<p>${escapeHtml(application)}</p>`).join('')}<p class="small">${escapeHtml(lemma.evidence_boundary || '')}</p><p>${sourceLink(lemma.source, 'Open the Lean theorem')}</p><details><summary>Lemma source and evidence hashes</summary><p>${escapeHtml(lemma.qualification || '')}</p><ul class="tm-citations">${citationHtml(lemma.source)}${lemma.citations.map(citationHtml).join('')}</ul></details></article>`).join('')}`;
  }
  function sourcesHtml(data) {
    const sources = Array.isArray(data.sources) ? data.sources : Object.values(data.sources || {});
    return `<details><summary>Pair dataset provenance and scope</summary><p class="small">${escapeHtml(data.scope || '')}</p>${listHtml(data.assumptions)}${listHtml(data.limits)}<dl class="tm-source">${sources.map(source => `<dt>${sourceLink(source)}</dt><dd>SHA-256: <code>${escapeHtml(source.sha256 || '')}</code>${source.hash_encoding ? `<br>Hash encoding: ${escapeHtml(source.hash_encoding)}` : ''}</dd>`).join('')}</dl><p><a href="tm-atlas-data.json" download>Download the complete pair dataset ↓</a></p></details>`;
  }
  function summaryText(pair) {
    const value = observations(pair);
    return `First halting step ${value.halting_time.equal ? 'matches' : 'differs'}; complete tape ${value.tape.equal ? 'matches' : 'differs'}; head position ${value.head_position.equal ? 'matches' : 'differs'}.`;
  }
  const api = { PROPERTIES, escapeHtml, sourceUrl, sourceHref, claimAnchor, traceAnchor, lemmaAnchor, observations, claimsForPair, validData, comparisonHtml, tapeBounds, tapeHtml, finalTapesHtml, claimsHtml, traceHtml, lemmasHtml, sourcesHtml, summaryText };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  if (typeof document === 'undefined') return;
  const byId = id => document.getElementById(id);
  const data = window.TM_ATLAS_DATA, loading = byId('tm-loading'), app = byId('tm-app');
  if (!loading || !app) return;
  if (!validData(data)) {
    loading.innerHTML = 'The saved machine comparisons are unavailable or inconsistent. Keep tm-atlas-data.js next to this page, or <a href="https://github.com/Maverick0351a/finite-congruence-checks/blob/main/evidence/tm-atlas-v1.json">inspect the saved pair records on GitHub</a>.';
    return;
  }
  const selector = byId('tm-pair-select');
  selector.innerHTML = data.pairs.map(pair => `<option value="${escapeHtml(pair.id)}">${escapeHtml(pair.name)}</option>`).join('');
  let selected = null;
  function renderPair(pair) {
    selected = pair;
    selector.value = pair.id;
    const claims = claimsForPair(data, pair);
    byId('tm-pair-id').textContent = pair.id;
    byId('tm-pair-title').textContent = pair.name;
    byId('tm-summary').textContent = summaryText(pair);
    byId('tm-properties').innerHTML = comparisonHtml(pair, claims);
    byId('tm-final-tapes').innerHTML = finalTapesHtml(pair);
    byId('tm-claims').innerHTML = claimsHtml(pair, claims);
    byId('tm-traces').innerHTML = '<h4>Exact saved traces</h4>' + ['left', 'right'].map(side => traceHtml(pair, side)).join('');
    byId('tm-lemmas').innerHTML = lemmasHtml(pair, claims);
    byId('tm-sources').innerHTML = sourcesHtml(data);
  }
  function revealHash() {
    let anchor;
    try { anchor = decodeURIComponent(window.location.hash.slice(1)); } catch (_) { return; }
    if (!/^tm-(trace|claim|lemma)-/.test(anchor)) return;
    const pair = data.pairs.find(item => {
      const claims = claimsForPair(data, item);
      return ['left', 'right'].some(side => item[side].trace.some(record => traceAnchor(item, side, record.steps) === anchor))
        || claims.some(claim => claimAnchor(claim) === anchor || claim.applicable_lemmas.some(lemma => lemmaAnchor(item, lemma) === anchor));
    });
    if (!pair) return;
    if (pair !== selected) renderPair(pair);
    const target = byId(anchor);
    if (!target) return;
    for (let parent = target.parentElement; parent; parent = parent.parentElement) if (parent.tagName === 'DETAILS') parent.open = true;
    target.scrollIntoView({ block: 'center' });
    target.focus({ preventScroll: true });
  }
  selector.addEventListener('change', () => {
    renderPair(data.pairs.find(pair => pair.id === selector.value) || data.pairs[0]);
    let anchor;
    try { anchor = decodeURIComponent(window.location.hash.slice(1)); } catch (_) { return; }
    // Explicit selection leaves the previous evidence target; replaceState avoids scrolling.
    if (/^tm-(trace|claim|lemma)-/.test(anchor)) window.history.replaceState(window.history.state, '', '#turing');
  });
  window.addEventListener('hashchange', revealHash);
  app.addEventListener('click', event => {
    const link = event.target.closest('a[href^="#tm-"]');
    if (link && link.getAttribute('href') === window.location.hash) revealHash();
  });
  loading.hidden = true;
  app.hidden = false;
  renderPair(data.pairs[0]);
  revealHash();
})();
