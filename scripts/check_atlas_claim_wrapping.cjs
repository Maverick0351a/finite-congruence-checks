/* Source contract for long claim identifiers. This does not perform layout.
 * Browser acceptance must repeat the closed/open C4 inspector at 390px.
 */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

function rules(css, conditional = false) {
  css = css.replace(/\/\*[\s\S]*?\*\//g, '');
  const result = [];
  let position = 0;
  while (position < css.length) {
    const open = css.indexOf('{', position);
    if (open < 0) { assert(!css.slice(position).trim(), 'Complete CSS rule'); break; }
    const selector = css.slice(position, open).trim();
    let end = open + 1, depth = 1;
    while (end < css.length && depth) {
      if (css[end] === '{') depth++;
      if (css[end] === '}') depth--;
      end++;
    }
    assert.equal(depth, 0, 'Balanced CSS');
    const body = css.slice(open + 1, end - 1);
    if (selector.startsWith('@')) {
      assert(selector.startsWith('@media'), 'Only existing media at-rules are modeled');
      result.push(...rules(body, true));
    } else {
      const declarations = body.split(';').filter(part => part.trim()).map(part => {
        const colon = part.indexOf(':');
        assert(colon > 0, 'Complete CSS declaration');
        const property = part.slice(0, colon).trim();
        // Ordinary property names are ASCII case-insensitive; custom names are not.
        const key = property.startsWith('--') ? property : property.replace(/[A-Z]/g, letter => letter.toLowerCase());
        return [key, part.slice(colon + 1).trim()];
      });
      for (const part of selector.split(',')) result.push({selector: part.trim().replace(/\s+/g, ' '), conditional, declarations});
    }
    position = end;
  }
  return result;
}

function wrappingContract(css) {
  const parsed = rules(css);
  for (const selector of ['#entry-claims summary', '#entry-claims caption']) {
    const applicable = parsed.filter(rule => rule.selector === selector);
    // Deliberately an explicit, conservative source contract, not a CSS engine:
    // a universal rule is required so narrow and desktop labels both wrap.
    assert(applicable.some(rule => !rule.conditional && rule.declarations.some(([key, value]) => key === 'overflow-wrap' && value === 'anywhere')),
      `Long claim label needs unconditional anywhere wrapping: ${selector}`);
    for (const rule of applicable) {
      for (const [key, value] of rule.declarations) {
        if (key === 'overflow-wrap') assert.equal(value, 'anywhere', `No conflicting label wrap: ${selector}`);
        if (key === 'white-space') assert.equal(value, 'normal', `No unbreakable label whitespace: ${selector}`);
        if (['overflow', 'overflow-x'].includes(key)) assert.equal(value, 'visible', `Do not clip or scroll claim labels: ${selector}`);
      }
    }
  }
  return true;
}

function checkAtlasClaimWrapping(root) {
  const read = name => fs.readFileSync(path.join(root, name), 'utf8');
  const html = read('space/atlas.html');
  const styles = [...html.matchAll(/<link\b[^>]*rel="stylesheet"[^>]*href="([^"]+)"/g)].map(match => match[1]);
  assert.deepEqual(styles, ['atlas.css', 'atlas-research.css'], 'Actual stylesheet order');
  const css = styles.map(name => read(`space/${name}`)).join('\n');
  wrappingContract(css);
  const app = require(path.join(root, 'space/atlas.js'));
  const data = JSON.parse(read('space/atlas-data.json'));
  const registry = JSON.parse(read('space/atlas-claims.json'));
  let labels = 0;
  for (const entry of data.entries) {
    const markup = app.claimsHtml(registry, entry);
    for (const claim of app.claimsForEntry(registry, entry)) {
      assert(markup.includes(`<summary>Inspect ${claim.id}: hypotheses, citations and evidence gates</summary>`), 'Exact complete claim ID remains in summary');
      assert(markup.includes(`<caption>Evidence supplied for ${claim.id}</caption>`), 'Exact complete claim ID remains in caption');
      labels += 2;
    }
  }
  const comparison = app.claimsForEntry(registry, data.entries.find(entry => entry.id === 'n4-E16457')).find(claim => claim.kind === 'same_shape_comparison');
  assert(comparison && /[a-f0-9]{64}/.test(comparison.id), 'Retain the actual long C4 comparison identifier from the live reproduction');
  // These reject missing caption/summary coverage, break-word (which does not
  // lower min-content width), a viewport-only patch, and later contradictory rules.
  const good = '#entry-claims summary,#entry-claims caption{overflow-wrap:anywhere}';
  const rejected = [
    '#entry-claims summary{overflow-wrap:anywhere}',
    '#entry-claims caption{overflow-wrap:anywhere}',
    good.replace('anywhere', 'break-word'),
    `@media(max-width:760px){${good}}`,
    good + '#entry-claims caption{white-space:nowrap}',
    good + '#entry-claims summary{overflow-wrap:normal}',
    good + '#entry-claims caption{overflow:hidden}',
    good + '#entry-claims caption{WHITE-SPACE:nowrap}',
    good + '#entry-claims summary{Overflow-Wrap:normal}',
    good + '#entry-claims caption{OVERFLOW-X:hidden}',
  ];
  for (const broken of rejected) assert.throws(() => wrappingContract(broken), assert.AssertionError);
  assert(wrappingContract(good.replace('overflow-wrap', 'OVERFLOW-WRAP')), 'Uppercase ordinary property retains the valid rule');
  assert.deepEqual(rules('#entry-claims caption{--MixedCase:A;--mixedcase:B}')[0].declarations,
    [['--MixedCase', 'A'], ['--mixedcase', 'B']], 'Distinct custom-property names preserve case (MC-R1)');
  console.log(`Atlas claim wrapping source contract: ${data.entries.length} entries, ${labels} exact labels, ${rejected.length} rejection controls, two property-case positive controls. No browser layout or mobile acceptance is inferred.`);
  return {entries: data.entries.length, labels, rejectionControls: rejected.length, propertyCasePositives: 2};
}
module.exports = {wrappingContract, checkAtlasClaimWrapping};
if (require.main === module) checkAtlasClaimWrapping(path.resolve(process.argv[2] || path.join(__dirname, '..')));
