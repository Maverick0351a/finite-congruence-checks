/* Source-level color regression for the Atlas. Not a browser or a WCAG audit.
 * Resolves the checked CSS subset (cascade, inheritance, vars, media, solid
 * colors) against static HTML and generated operation/claim/SVG markup.
 * Layout, native widgets, canvas, paint order and assistive technology remain
 * separate browser checks. Unsupported checked color values/selectors fail.
 */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

function parseHtml(html, parent = null) {
  const document = parent || {tag: 'document', attrs: {}, children: [], parent: null, states: new Set()};
  const stack = [document];
  for (const token of html.matchAll(/<!--[\s\S]*?-->|<![^>]*>|<\/?[\w-]+\b[^>]*>/g)) {
    const text = token[0];
    if (text.startsWith('<!')) continue;
    const tag = /^<\/?([\w-]+)/.exec(text)[1].toLowerCase();
    if (text.startsWith('</')) {
      assert.equal(stack.at(-1).tag, tag, `Balanced fixture markup: ${tag}`);
      stack.pop(); continue;
    }
    const attrs = {};
    for (const m of text.slice(tag.length + 1).matchAll(/([\w-]+)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s>]+)))?/g)) {
      attrs[m[1]] = m[2] ?? m[3] ?? m[4] ?? '';
    }
    const node = {tag, attrs, parent: stack.at(-1), children: [], states: new Set()};
    node.parent.children.push(node);
    if (!text.endsWith('/>') && !['meta', 'link', 'img', 'br', 'hr', 'input'].includes(tag)) stack.push(node);
  }
  assert.equal(stack.length, 1, 'Balanced fixture document');
  return document;
}
function descendants(node) { return node.children.flatMap(child => [child, ...descendants(child)]); }
function parts(selector) {
  return selector.trim().replace(/\s*>\s*/g, ' > ').split(/\s+/).filter(Boolean);
}
const checkedProperty = key => key.startsWith('--') ||
  ['color', 'background', 'background-color', 'fill', 'stroke', 'border-color', 'outline-color'].includes(key);
function checkedSelector(selector) {
  // This existing separator is decorative generated content, not a fixture
  // element. Exclude exactly this selector, not arbitrary pseudo-elements or
  // sibling selectors that could otherwise conceal a checked color override.
  if (selector.replace(/\s+/g, '') === '.metrics>div+div:before') return false;
  const tokens = parts(selector);
  const unsupported = () => new Error(`Unsupported checked color selector: ${selector}`);
  if (!tokens.length) throw unsupported();
  for (let i = 0; i < tokens.length; i++) {
    if (tokens[i] === '>') {
      if (!i || i === tokens.length - 1 || tokens[i - 1] === '>') throw unsupported();
      continue;
    }
    if (tokens[i] === '*') continue;
    let rest = tokens[i].replace(/^[\w-]+/, '');
    // Validate the whole selector before matching any node: a class mismatch
    // must not hide unsupported syntax later in the same compound selector.
    while (rest) {
      const m = /^(?:[.#][\w-]+|\[[\w-]+(?:=(?:"[\w-]+"|'[\w-]+'|[\w-]+))?\]|:nth-child\(\d+\)|:(?:root|first-child|hover|focus-visible|focus|disabled|target)(?![\w-]|\())/.exec(rest);
      if (!m) throw unsupported();
      rest = rest.slice(m[0].length);
    }
  }
  return true;
}
function simple(node, selector) {
  if (selector === '*') return true;
  let rest = selector;
  const tag = /^[\w-]+/.exec(rest);
  if (tag) { if (tag[0] !== node.tag) return false; rest = rest.slice(tag[0].length); }
  while (rest) {
    let m;
    if ((m = /^([.#])([\w-]+)/.exec(rest))) {
      if (m[1] === '#' ? node.attrs.id !== m[2] : !(node.attrs.class || '').split(/\s+/).includes(m[2])) return false;
    } else if ((m = /^\[([\w-]+)(?:=(?:"([^"]*)"|'([^']*)'|([^\]]+)))?\]/.exec(rest))) {
      if (!(m[1] in node.attrs)) return false;
      if (m[2] !== undefined || m[3] !== undefined || m[4] !== undefined) {
        if (node.attrs[m[1]] !== (m[2] ?? m[3] ?? m[4])) return false;
      }
    } else if ((m = /^:([\w-]+)(?:\((\d+)\))?/.exec(rest))) {
      if (m[1] === 'root') { if (node.tag !== 'html') return false; }
      else if (m[1] === 'first-child' || m[1] === 'nth-child') {
        if (node.parent?.children.indexOf(node) !== (m[1] === 'first-child' ? 0 : Number(m[2]) - 1)) return false;
      } else if (!node.states.has(m[1])) return false;
    } else throw new Error(`Unsupported checked selector: ${selector}`);
    rest = rest.slice(m[0].length);
  }
  return true;
}
function matches(node, selector) {
  const tokens = parts(selector);
  function visit(current, i) {
    if (!current || !simple(current, tokens[i])) return false;
    if (i === 0) return true;
    if (tokens[i - 1] === '>') return visit(current.parent, i - 2);
    for (let p = current.parent; p; p = p.parent) if (visit(p, i - 1)) return true;
    return false;
  }
  return visit(node, tokens.length - 1);
}
function specificity(selector) {
  const attrs = selector.match(/\[[^\]]*\]/g) || [];
  const plain = selector.replace(/\[[^\]]*\]/g, '').replace(/:[\w-]+(?:\([^)]*\))?/g, '');
  return [(plain.match(/#[\w-]+/g) || []).length,
    attrs.length + (plain.match(/\.[\w-]+/g) || []).length + (selector.match(/:[\w-]+/g) || []).length,
    (plain.replace(/[.#][\w-]+/g, '').match(/\b[a-z][\w-]*/gi) || []).length];
}
function activeMedia(query, env) {
  const tests = [...query.matchAll(/\(([\w-]+)\s*:\s*([\w-]+)\)/g)];
  assert(tests.length, `Known media query: ${query}`);
  return tests.every(([, key, value]) => {
    if (key === 'max-width') return env.width <= Number(value.replace('px', ''));
    if (key === 'prefers-color-scheme') return env.scheme === value;
    if (key === 'forced-colors') return (env.forced ? 'active' : 'none') === value;
    if (key === 'prefers-reduced-motion') return value === 'reduce';
    throw new Error(`Unsupported media feature: ${key}`);
  });
}
function parseCss(css, env) {
  css = css.replace(/\/\*[\s\S]*?\*\//g, '');
  const rules = [];
  function block(start, end) {
    let pos = start;
    while (pos < end) {
      const open = css.indexOf('{', pos);
      if (open < 0 || open >= end) break;
      const head = css.slice(pos, open).trim();
      let close = open + 1, depth = 1;
      while (close < end && depth) { if (css[close] === '{') depth++; if (css[close] === '}') depth--; close++; }
      assert.equal(depth, 0, 'Balanced CSS blocks');
      if (head.startsWith('@media')) {
        if (activeMedia(head.slice(6), env)) block(open + 1, close - 1);
      } else {
        assert(!head.startsWith('@'), `Unsupported CSS at-rule: ${head}`);
        const declarations = css.slice(open + 1, close - 1).split(';').map(part => {
          const colon = part.indexOf(':');
          return colon < 0 ? null : [part.slice(0, colon).trim(), part.slice(colon + 1).trim()];
        }).filter(Boolean);
        // Layout-only rules are outside the checked color subset. Validate
        // color selectors up front, even when no fixture currently matches.
        if (declarations.some(([key]) => checkedProperty(key))) {
          for (const selector of head.split(',')) {
            if (checkedSelector(selector)) rules.push({selector: selector.trim(), declarations, score: specificity(selector)});
          }
        }
      }
      pos = close;
    }
  }
  block(0, css.length);
  return rules;
}
function resolver(rules) {
  const cache = new Map();
  function style(node) {
    if (cache.has(node)) return cache.get(node);
    assert(!/(?:color|background|fill|stroke)\s*:/.test(node.attrs.style || ''), 'Inline component colors need explicit checker support');
    const inherited = node.parent ? style(node.parent) : {};
    const result = Object.fromEntries(Object.entries(inherited).filter(([key]) => key.startsWith('--') || ['color', 'fill', 'stroke'].includes(key)));
    const winners = new Map();
    rules.forEach((rule, order) => {
      if (!matches(node, rule.selector)) return;
      for (const [position, declaration] of rule.declarations.entries()) {
        let [key, value] = declaration;
        if (!checkedProperty(key)) continue;
        if (key === 'background') key = 'background-color';
        const important = /!important\s*$/.test(value) ? 1 : 0;
        value = value.replace(/\s*!important\s*$/, '');
        const score = [important, ...rule.score, order, position];
        const old = winners.get(key);
        if (!old || score.some((v, i) => v !== old.score[i] && score.slice(0, i).every((x, j) => x === old.score[j]) && v > old.score[i])) {
          winners.set(key, {score, value});
        }
      }
    });
    for (const [key, item] of winners) result[key] = item.value;
    cache.set(node, result);
    return result;
  }
  function value(node, key) {
    const s = style(node);
    function resolve(v, depth = 0) {
      assert(depth < 20, 'No variable cycle');
      return v?.replace(/var\((--[\w-]+)\)/g, (_, name) => {
        assert(s[name] !== undefined, `Defined CSS variable: ${name}`);
        return resolve(s[name], depth + 1);
      });
    }
    return resolve(s[key]);
  }
  function background(node) {
    const color = value(node, 'background-color');
    if (color && color !== 'transparent') return color;
    assert(node.parent, 'Known opaque background');
    return background(node.parent);
  }
  return {value, background};
}
function rgb(value) {
  const named = {white: '#ffffff', black: '#000000'};
  value = named[value] || value;
  assert(/^#[a-f0-9]{3}$|^#[a-f0-9]{6}$/i.test(value), `Supported opaque solid color: ${value}`);
  if (value.length === 4) value = '#' + [...value.slice(1)].map(c => c + c).join('');
  return value.slice(1).match(/../g).map(c => parseInt(c, 16) / 255);
}
function contrast(a, b) {
  const luminance = value => rgb(value).map(c => c <= 0.04045 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4)
    .reduce((sum, c, i) => sum + c * [0.2126, 0.7152, 0.0722][i], 0);
  const x = luminance(a), y = luminance(b);
  return (Math.max(x, y) + 0.05) / (Math.min(x, y) + 0.05);
}
function inspect(root, overrides = {}) {
  const read = name => fs.readFileSync(path.join(root, name), 'utf8');
  const html = read('space/atlas.html');
  const styles = [...html.matchAll(/<link\b[^>]*rel="stylesheet"[^>]*href="([^"]+)"/g)].map(m => m[1]);
  assert.deepEqual(styles, ['atlas.css', 'atlas-research.css'], 'Check the actual stylesheet order');
  const css = styles.map(name => overrides[name] ?? read(`space/${name}`)).join('\n');
  const document = parseHtml(html), all = () => descendants(document);
  const one = selector => { const found = all().filter(node => matches(node, selector)); assert(found.length, `Existing component: ${selector}`); return found[0]; };
  const app = require(path.join(root, 'space/atlas.js'));
  const data = JSON.parse(read('space/atlas-data.json'));
  const registry = JSON.parse(read('space/atlas-claims.json'));
  const entry = data.entries.find(item => item.operations.length && item.partitions.length > 1);
  parseHtml(app.operationHtml(entry.operations[0], 0), one('#entry-operations'));
  parseHtml(app.latticeSvg(entry, 0), one('#entry-diagram'));
  parseHtml(app.claimsHtml(registry, entry), one('#entry-claims'));
  // Control structure mirrors the dynamic button's documented class/ARIA path;
  // selection/markup generation itself is covered by check_atlas_selection.cjs.
  parseHtml('<button aria-pressed="false"><strong>Entry</strong><span>Summary</span></button>', one('#entry-list'));
  const catalogButton = one('#entry-list button');
  const textCases = [
    ['skip link', '.skip'], ['catalog label', '.catalog label'], ['catalog count', '#entry-count'],
    ['catalog select', '.catalog select'], ['entry title', '#entry-title'], ['status', '.status'],
    ['pill', '.pill'], ['operation', '.operation'], ['operation label', '.operation>strong'],
    ['operation mapping', '.mapping-row span'], ['operation arrow', '.mapping-row b'],
    ['takeaway', '.takeaway p'], ['takeaway label', '.takeaway>span'], ['entry takeaway', '.entry-takeaway'],
    ['preformatted data', '#entry-json'], ['reproduction commands', '#reproduce-commands'],
    ['claim statement', '.claim-record p'], ['claim code', '.claim-record code'],
    ['claim header', '.claim-gates th'], ['claim value', '.claim-gates td'], ['claim caption', '.claim-gates caption'],
    ['primary button', '.primary'], ['secondary button', '.secondary'],
  ];
  const results = [], failures = [];
  for (const env of [
    {scheme: 'light', width: 1280, forced: false}, {scheme: 'dark', width: 1280, forced: false},
    {scheme: 'light', width: 600, forced: false}, {scheme: 'dark', width: 600, forced: false},
  ]) {
    function check(name, fg, bg, minimum = 4.5) {
      const ratio = contrast(fg, bg), item = {environment: `${env.scheme}/${env.width}`, name, foreground: fg, background: bg, ratio, minimum};
      results.push(item); if (ratio < minimum) failures.push(item);
    }
    const get = () => resolver(parseCss(css, env));
    let colors = get();
    for (const [name, selector] of textCases) { const node = one(selector); check(name, colors.value(node, 'color'), colors.background(node)); }
    for (const state of ['normal', 'hover', 'selected', 'selected-hover']) {
      catalogButton.states = new Set(state.includes('hover') ? ['hover'] : []);
      catalogButton.attrs['aria-pressed'] = state.includes('selected') ? 'true' : 'false';
      colors = get();
      for (const node of [catalogButton, ...catalogButton.children]) check(`catalog ${state} ${node.tag}`, colors.value(node, 'color'), colors.background(node));
    }
    catalogButton.states.clear(); catalogButton.attrs['aria-pressed'] = 'false';
    for (const selector of ['.primary', '.secondary']) {
      const node = one(selector); node.states.add('hover'); colors = get();
      check(`${selector} hover`, colors.value(node, 'color'), colors.background(node)); node.states.clear();
    }
    for (const selector of ['.skip', '.primary', '.secondary', '.catalog select', '.lattice-scroll', 'summary']) {
      const node = one(selector); node.states = new Set(['focus', 'focus-visible']); colors = get();
      check(`${selector} keyboard focus text`, colors.value(node, 'color'), colors.background(node));
      // The outline has a positive offset in the stylesheet; compare its color
      // with the surrounding parent surface, not the button's interior fill.
      check(`${selector} focus outline`, colors.value(node, 'outline-color'), colors.background(node.parent), 3);
      node.states.clear();
    }
    colors = get();
    for (const node of all().filter(item => matches(item, '.lattice-node'))) {
      const rect = node.children.find(item => item.tag === 'rect'), fill = colors.value(rect, 'fill');
      for (const label of node.children.filter(item => item.tag === 'text')) check(`SVG ${node.attrs.class} ${label.attrs.class || 'label'}`, colors.value(label, 'fill'), fill);
      check('SVG node outline', colors.value(rect, 'stroke'), colors.background(one('.lattice-scroll')), 3);
    }
    check('SVG edge', colors.value(one('.lattice-edge'), 'stroke'), colors.background(one('.lattice-scroll')), 3);
  }
  // System colors cannot be reduced to fixed RGB without the user's palette.
  // Require source-resolved symbolic pairs for the repaired and SVG paths.
  const forced = resolver(parseCss(css, {scheme: 'dark', width: 600, forced: true}));
  const systemColors = [];
  for (const selector of ['.skip', '.operation', '#entry-json']) {
    const node = one(selector);
    const foreground = forced.value(node, 'color'), background = forced.background(node);
    const passed = ['CanvasText', 'LinkText', 'ButtonText'].includes(foreground) && ['Canvas', 'ButtonFace'].includes(background);
    const item = {environment: 'forced-colors', name: selector, foreground, background, passed};
    systemColors.push(item); if (!passed) failures.push(item);
  }
  const edge = {environment: 'forced-colors', name: 'SVG edge', stroke: forced.value(one('.lattice-edge'), 'stroke')};
  edge.passed = edge.stroke === 'CanvasText';
  systemColors.push(edge); if (!edge.passed) failures.push(edge);
  return {results, systemColors, failures, minText: Math.min(...results.filter(item => item.minimum === 4.5).map(item => item.ratio)),
    minGraphic: Math.min(...results.filter(item => item.minimum === 3).map(item => item.ratio)),
    limits: 'Source cascade/solid-color fixtures only; no browser rendering, native-widget, canvas, layout or assistive-technology acceptance.'};
}
function checkAtlasContrast(root) {
  const result = inspect(root);
  assert.deepEqual(result.failures, [], 'Component contrast regression');
  const css = fs.readFileSync(path.join(root, 'space/atlas-research.css'), 'utf8');
  const controls = [
    ['skip link', '.skip{background:white;color:var(--accent)}'],
    ['.skip keyboard focus text', '.skip:focus{background:white;color:var(--accent)}'],
    ['operation', '.operation{background:#f0f4fc}'],
    ['preformatted data', 'pre{background:#eaf0fa}'],
    ['catalog hover button', '.entry-list button:hover{background:white}'],
  ];
  for (const [name, rule] of controls) {
    const broken = inspect(root, {'atlas-research.css': css + '\n' + rule});
    assert(broken.failures.some(item => item.name === name && item.ratio < 4.5), `Reject reintroduced ${name} failure`);
  }
  const svg = inspect(root, {'atlas-research.css': css + '\n.lattice-node rect{fill:white}'});
  assert(svg.failures.some(item => item.name === 'SVG lattice-node label'), 'Reject pale SVG node fill');
  assert(!svg.failures.some(item => item.name === 'SVG lattice-node selected label'), 'More-specific selected fill wins despite later generic rule');
  const mobile = inspect(root, {'atlas-research.css': css + '\n@media(max-width:760px){.operation{background:white}}'});
  assert(mobile.failures.some(item => item.name === 'operation' && item.environment === 'light/600'), 'Mobile-only color failure detected');
  assert(!mobile.failures.some(item => item.name === 'operation' && item.environment === 'light/1280'), 'Inactive width query excluded');
  const duplicate = inspect(root, {'atlas-research.css': css + '\n.operation{background:var(--surface-soft);background:white}'});
  assert(duplicate.failures.some(item => item.name === 'operation'), 'Last same-priority declaration wins (CR-R1)');
  for (const rule of [
    '.operation{background:white;background:var(--surface-soft)}',
    '.operation{background:var(--surface-soft)!important;background:white}',
  ]) {
    const valid = inspect(root, {'atlas-research.css': css + '\n' + rule});
    assert.deepEqual(valid.failures, [], 'Later declaration and earlier !important controls preserve valid colors');
  }
  for (const selector of ['.operation:not(.disabled)', '.absent:not(.disabled)', '.operation:unsupported', '.operation+.operation']) {
    assert.throws(() => inspect(root, {'atlas-research.css': css + `\n${selector}{background:white}`}),
      /Unsupported checked color selector:/, `Unsupported color selector fails explicitly (CR-R2): ${selector}`);
  }
  console.log(`Atlas component color checks: ${result.results.length} pairings, eight color regressions, four unsupported-selector rejections and two cascade positives; text >= ${result.minText.toFixed(2)}:1; SVG/focus contrast >= ${result.minGraphic.toFixed(2)}:1. ${result.limits}`);
  return result;
}
module.exports = {inspect, checkAtlasContrast, contrast};
if (require.main === module) {
  const root = path.resolve(process.argv[2] || path.join(__dirname, '..'));
  const result = inspect(root, process.argv[3] ? {'atlas-research.css': fs.readFileSync(process.argv[3], 'utf8')} : {});
  console.log(JSON.stringify(result, null, 2));
  if (result.failures.length) process.exitCode = 1;
}
