// Drive the pinned Glitnir renderer and its Export HTML over prepared snapshots.
// The renderer only reads: every request it makes is answered from the inputs.
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const {readFileSync} = require('node:fs');
const path = require('node:path');
const {JSDOM} = require('jsdom');

const ROOT = path.resolve(__dirname, '../..');
const NOTEBOOK_NAVIGATION_CSS = readFileSync(path.join(ROOT, 'gallery/notebook-navigation.css'), 'utf8');
// Glitnir's own words for saved results that were not compared with any environment.
const RECORDED = 'Saved results, shown as recorded';
const escape = value => String(value).replace(/[&<>"']/g, char => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[char]));
const TOPICS = {
  basics: ['Start here', 'Small models introduce claims, saved evidence and refutations.'],
  biochemistry: ['Biochemistry', "A molecular controller's output bounded for all time: one certified cell checked, the full proof cited."],
  circuits: ['Circuits', 'Composition, contracts, rewrites and discrete dynamics.'],
  dynamics: ['Dynamical systems', 'Continuous trajectories and their bounds.'],
  finance: ['Finance', 'A hedged book bounded under every shock in a band, bounds on the odds of its stop under random shocks, and a hedge that covers an option on every path within a daily move band, all as theorems.'],
  galerkin: ['Galerkin models', 'Finite-dimensional fluid models, energy and enstrophy.'],
  pdes: ['Partial differential equations', 'Stream contracts, formal expansions and analytic certificates.'],
};
// Walkthroughs of other people's Lean projects, by folder under walkthroughs/: unchecked.
const WALKTHROUGHS_TITLE = 'Walkthroughs of existing formalizations';
const WALKTHROUGHS_INTRO = 'Guided readings of Lean projects that Glitnir cannot check. Unchecked: each claim is compared with the original only as text, and nothing here was compiled.';
const WALKTHROUGHS = {
  eth: 'A 2^o(n)-time algorithm for 3-SAT and the failure of the Exponential Time Hypothesis, through the Lean project eth of anthropics/formal-math.',
  '3sum-apsp': 'Truly subquadratic 3SUM and truly subcubic APSP through triangles in sparse lopsided graphs, through the Lean project 3sum-apsp of anthropics/formal-math.',
};

function rewriteReferences(content, notebooks) {
  for (const link of content.querySelectorAll('a[href]')) {
    const url = new URL(link.getAttribute('href'), 'https://export.invalid');
    if (url.origin !== 'https://export.invalid' || url.pathname !== '/') continue;
    const module = url.searchParams.get('reference') || url.searchParams.get('notebook');
    const target = notebooks.find(item => item.snapshot.file === `${module}.lean`);
    if (target) link.href = `https://gallery.invalid/${target.html}`;
  }
}

// Glitnir's renderer shows a Markdown link to another site as its source text.
// On walkthrough pages, turn such text outside code and mathematics into links.
const MARKDOWN_LINK = /\[([^\]\n]+)\]\((https:\/\/[^)\s]+)\)/g;
function linkMarkdown(doc, root) {
  const walker = doc.createTreeWalker(root, doc.defaultView.NodeFilter.SHOW_TEXT);
  const nodes = [];
  while (walker.nextNode()) {
    if (!walker.currentNode.parentElement.closest('a,code,pre,.math')) nodes.push(walker.currentNode);
  }
  for (const node of nodes) {
    const text = node.nodeValue;
    const matches = [...text.matchAll(MARKDOWN_LINK)];
    if (!matches.length) continue;
    const fragment = doc.createDocumentFragment();
    let at = 0;
    for (const match of matches) {
      fragment.append(text.slice(at, match.index));
      const link = doc.createElement('a');
      link.href = match[2];
      link.rel = 'noopener noreferrer';
      match[1].split('`').forEach((part, index) => {
        if (!part) return;
        if (index % 2) { const code = doc.createElement('code'); code.textContent = part; link.append(code); } else link.append(part);
      });
      fragment.append(link);
      at = match.index + match[0].length;
    }
    fragment.append(text.slice(at));
    node.replaceWith(fragment);
  }
}

const drawn = view => Boolean(view.querySelector('svg.circuit-scene, .view-body img'));
const unavailableNote = view => Boolean(view.querySelector('.note-line[data-tone="red"]'));

function validateExport(html, entry) {
  const dom = new JSDOM(html);
  try {
    const doc = dom.window.document;
    assert.equal(doc.querySelectorAll('script,iframe,object,embed,form,.view-wait,.katex-error').length, 0, 'Unsafe or incomplete export');
    assert.ok(doc.body.textContent.includes(entry.snapshot.sha256), 'Missing source fingerprint');
    if (entry.walkthrough) {
      // A walkthrough has no results: its notice says it is unchecked, never recorded.
      assert.ok(doc.body.textContent.includes(entry.snapshot.preview.notice), 'Walkthrough must be shown as unchecked');
      assert.ok(!doc.body.textContent.includes(RECORDED), 'A walkthrough has no saved results');
    } else assert.ok(doc.body.textContent.includes(RECORDED), 'Saved results must be shown as recorded');
    for (const claim of entry.snapshot.project_claims) {
      assert.ok(doc.getElementById(`cell-${claim.name}`), `Missing claim ${claim.name}`);
    }
    const views = [...doc.querySelectorAll('.view-cell')];
    assert.equal(views.length, entry.snapshot.views.length, 'Missing diagram');
    const failed = (entry.diagram_errors || []).length;
    assert.equal(views.filter(drawn).length, views.length - failed, 'Diagram has no drawing');
    assert.equal(views.filter(view => !drawn(view) && unavailableNote(view)).length, failed, 'Unavailable diagram has no note');
    for (const element of doc.querySelectorAll('*')) {
      for (const attribute of element.attributes) assert.ok(!/^on/i.test(attribute.name), 'Event handler in export');
    }
    for (const image of doc.images) assert.ok(image.src.startsWith('data:image/'), 'Image is not embedded');
  } finally { dom.window.close(); }
}

function addNotebookNavigation(doc, entry) {
  const app = doc.querySelector('.app');
  assert.ok(app, 'Missing notebook container');
  const nav = doc.createElement('nav');
  nav.className = 'gallery-nav';
  nav.setAttribute('aria-label', 'Notebook navigation');
  // Pages sit one folder deep (topic/), walkthroughs two (walkthroughs/name/).
  const index = '../'.repeat(Math.max(1, (entry.html || '').split('/').length - 1)) + 'index.html';
  const source = `<a class="gallery-source" href="${escape(entry.source_url)}" title="View ${escape(entry.snapshot.file)} on GitHub"><svg viewBox="0 0 20 20" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true" focusable="false"><path d="m7 5-5 5 5 5m6-10 5 5-5 5"/></svg><span>Lean source</span></a>`;
  const map = entry.walkthrough ? `<a class="gallery-source gallery-map" href="${escape(path.posix.basename(entry.walkthrough.map))}" title="The clickable map of the proof"><svg viewBox="0 0 20 20" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true" focusable="false"><circle cx="10" cy="4" r="2"/><circle cx="4" cy="16" r="2"/><circle cx="16" cy="16" r="2"/><path d="m9 6-4 8m6-8 4 8"/></svg><span>Map</span></a>` : '';
  nav.innerHTML = `<a class="gallery-back" href="${index}" aria-label="Back to notebook gallery"><svg viewBox="0 0 20 20" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true" focusable="false"><path d="m11 5-5 5 5 5M6 10h10"/></svg><span>Gallery</span></a>${map ? `<span class="gallery-actions">${map}${source}</span>` : source}`;
  app.prepend(nav);
  const style = doc.createElement('style');
  style.textContent = NOTEBOOK_NAVIGATION_CSS;
  doc.head.append(style);
}

// The renderer's scripts, as its page lists them and in that order. The page is the
// one list: Glitnir may split or rename its scripts between releases.
function rendererScripts(media) {
  const html = readFileSync(path.join(media, 'index.html'), 'utf8');
  return [...html.matchAll(/<script src="\/([^"]+)"><\/script>/g)].map(match => match[1]);
}

async function renderNotebook(manifest, entry) {
  const dom = new JSDOM(await fs.readFile(path.join(manifest.media, 'index.html'), 'utf8'), {
    runScripts: 'outside-only', url: 'https://export.invalid/',
  });
  const {window} = dom;
  const errors = [];
  let exported;
  window.addEventListener('error', event => errors.push(event.error));
  window.matchMedia = () => ({matches: false});
  window.HTMLElement.prototype.scrollIntoView = () => {};
  const schedule = window.setTimeout.bind(window);
  window.setTimeout = (callback, delay) => [250, 1000, 4000].includes(delay) ? 0 : schedule(callback, delay);
  const OriginalDate = window.Date;
  window.Date = class extends OriginalDate {
    constructor(...args) { super(...(args.length ? args : [manifest.timestamp])); }
  };
  const assetURL = url => {
    const parsed = new URL(url, 'https://export.invalid');
    const asset = entry.figures[parsed.searchParams.get('path')];
    assert.ok(asset && asset.sha256 === parsed.searchParams.get('sha256'), 'Missing or changed figure');
    return asset.url;
  };
  // The renderer's shared host interface, as the editor provides it.
  window.glitnirHost = {
    asset: async url => assetURL(url),
    saveHTML: async html => { exported = html; },
    fetch: async (url, options = {}) => {
      try {
        assert.equal(options.method || 'GET', 'GET', 'Export must never write or replay');
        const parsed = new URL(url, 'https://export.invalid');
        let json;
        if (url === '/api/notebook') json = entry.snapshot;
        else if (url === '/api/export/styles') json = {css: manifest.css};
        else if (parsed.pathname === '/api/view') {
          json = entry.drawings[`${parsed.searchParams.get('cell')}:${parsed.searchParams.get('line')}`];
          assert.ok(json, `Missing prepared diagram ${url}`);
        } else throw new Error(`Unexpected exporter request: ${url}`);
        return {ok: true, status: 200, json: async () => structuredClone(json)};
      } catch (error) { errors.push(error); throw error; }
    },
  };
  try {
    for (const script of rendererScripts(manifest.media)) {
      window.eval(await fs.readFile(path.join(manifest.media, script), 'utf8'));
    }
    const originalExport = window.glitnirExport;
    window.glitnirExport = async options => {
      // Glitnir drops live-editor URLs. Translate only known corpus references
      // through an inert HTTPS marker, then make them relative after export.
      rewriteReferences(options.content, manifest.notebooks);
      return originalExport(options);
    };
    const deadline = Date.now() + 30_000;
    while (!window.document.querySelector('#doc .cell') || window.document.querySelector('.view-wait')) {
      if (errors.length) throw errors[0];
      if (Date.now() > deadline) throw new Error(`Renderer timed out: ${entry.path}`);
      await new Promise(resolve => setTimeout(resolve, 10));
    }
    window.document.getElementById('export-html').click();
    while (!exported) {
      if (errors.length) throw errors[0];
      if (Date.now() > deadline) throw new Error(`Export failed: ${entry.path}: ${window.document.body.textContent.slice(-1000)}`);
      await new Promise(resolve => setTimeout(resolve, 10));
    }
    assert.deepEqual(errors, []);
    validateExport(exported, entry);
    const page = new JSDOM(exported);
    try {
      const doc = page.window.document;
      for (const link of doc.querySelectorAll('a[href^="https://gallery.invalid/"]')) {
        const target = new URL(link.href).pathname.slice(1);
        link.href = path.posix.relative(path.posix.dirname(entry.html), target);
      }
      if (entry.walkthrough) linkMarkdown(doc, doc.querySelector('main'));
      const snapshot = doc.querySelector('.snapshot');
      snapshot.textContent = snapshot.textContent.replace(' · exported ', ' · source revision dated ');
      addNotebookNavigation(doc, entry);
      return {html: '<!doctype html>\n' + doc.documentElement.outerHTML, title: doc.title};
    } finally { page.window.close(); }
  } finally { window.close(); }
}

function galleryIndex(manifest, entries) {
  const groups = Object.entries(TOPICS).map(([topic, [title, description]]) => {
    const notebooks = entries.filter(entry => entry.html.startsWith(topic + '/'));
    return `<section id="${topic}" class="topic"><header><h2>${title}</h2><p>${description}</p></header><ul>${notebooks.map(entry => `<li><a class="notebook-title" href="${escape(entry.html)}">${escape(entry.title)}</a></li>`).join('')}</ul></section>`;
  }).join('\n');
  // Only an edition that exports walkthroughs lists them.
  const guided = entries.filter(entry => entry.walkthrough);
  const walkthroughs = !guided.length ? '' : `<section id="walkthroughs" class="topic walkthroughs"><header><h2>${WALKTHROUGHS_TITLE}</h2><p>${WALKTHROUGHS_INTRO}</p></header><ul>${guided.map(entry => `<li class="walkthrough"><a class="notebook-title" href="${escape(entry.html)}">${escape(entry.title)}</a><p>${escape(WALKTHROUGHS[entry.walkthrough.name])}</p><a class="walkthrough-map" href="${escape(entry.walkthrough.map)}">Map of the proof</a></li>`).join('')}</ul></section>`;
  return readFileSync(path.join(ROOT, 'gallery/index.html'), 'utf8')
    .replace('{{topics}}', groups + (walkthroughs && '\n' + walkthroughs))
    .replace('{{walkthroughs-nav}}', guided.length ? '<a href="#walkthroughs">Walkthroughs</a>' : '')
    .replaceAll('{{repository}}', escape(manifest.repository))
    .replaceAll('{{revision}}', escape(manifest.revision));
}

async function copyGalleryAssets(output) {
  await fs.cp(path.join(ROOT, 'gallery/assets'), path.join(output, 'assets'), {recursive: true});
  await fs.copyFile(path.join(ROOT, 'gallery/triptych-transcript.html'), path.join(output, 'triptych-transcript.html'));
  await fs.mkdir(path.join(output, 'receipts'), {recursive: true});
  await fs.copyFile(path.join(ROOT, 'releases/proved-refuted-unknown.json'), path.join(output, 'receipts/proved-refuted-unknown.json'));
}

async function main(inputs, output) {
  const manifest = JSON.parse(await fs.readFile(inputs, 'utf8'));
  const entries = [];
  await fs.mkdir(output, {recursive: true});
  for (const entry of manifest.notebooks) {
    if (entry.walkthrough) assert.ok(WALKTHROUGHS[entry.walkthrough.name], `Undescribed walkthrough: ${entry.html}`);
    else assert.ok(TOPICS[entry.html.split('/')[0]], `Unknown gallery topic: ${entry.html}`);
    const rendered = await renderNotebook(manifest, entry);
    const destination = path.join(output, entry.html);
    await fs.mkdir(path.dirname(destination), {recursive: true});
    await fs.writeFile(destination, rendered.html);
    // The walkthrough's committed clickable map, published beside its page.
    if (entry.walkthrough) await fs.copyFile(path.join(ROOT, entry.walkthrough.map), path.join(output, entry.walkthrough.map));
    entries.push({html: entry.html, title: rendered.title, source_url: entry.source_url,
      source_sha256: entry.snapshot.sha256, claims: entry.snapshot.project_claims.length,
      diagrams: entry.snapshot.views.length, unavailable_diagrams: (entry.diagram_errors || []).length,
      ...(entry.walkthrough ? {walkthrough: entry.walkthrough, unchecked_notice: entry.snapshot.preview.notice} : {})});
    console.log(`Exported ${entry.html}`);
  }
  await fs.writeFile(path.join(output, 'index.html'), galleryIndex(manifest, entries));
  await fs.copyFile(path.join(ROOT, 'gallery/gallery.css'), path.join(output, 'gallery.css'));
  await copyGalleryAssets(output);
  await fs.copyFile(path.join(ROOT, 'LICENSE'), path.join(output, 'LICENSE'));
  await fs.writeFile(path.join(output, '.nojekyll'), '');
  await fs.writeFile(path.join(output, 'manifest.json'), JSON.stringify({repository: manifest.repository, revision: manifest.revision, notebooks: entries}, null, 2) + '\n');
}

module.exports = {copyGalleryAssets, addNotebookNavigation, validateExport, galleryIndex, linkMarkdown, renderNotebook, rendererScripts, rewriteReferences, WALKTHROUGHS};
if (require.main === module) main(...process.argv.slice(2)).catch(error => { console.error(error); process.exitCode = 1; });
