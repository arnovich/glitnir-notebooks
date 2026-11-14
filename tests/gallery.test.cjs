const assert = require('node:assert/strict');
const {test} = require('node:test');
const {JSDOM} = require('jsdom');
const {copyGalleryAssets, addNotebookNavigation, validateExport, galleryIndex, linkMarkdown, rendererScripts, rewriteReferences, WALKTHROUGHS} = require('../scripts/gallery/render.cjs');
const {mkdtempSync, writeFileSync} = require('node:fs');
const os = require('node:os');
const path = require('node:path');

test('export validation refuses missing claims, scripts and incomplete diagrams', () => {
  const entry = {snapshot: {sha256: 'abc', project_claims: [{name: 'first'}], views: []}};
  const valid = '<p>abc · Saved results, shown as recorded.</p><section id="cell-first">Open goal</section>';
  assert.doesNotThrow(() => validateExport(valid, entry));
  for (const html of [valid.replace('cell-first', 'lost'), valid.replace('shown as recorded', 'current'), valid + '<script>x()</script>', valid + '<p class="view-wait">Drawing</p>']) {
    assert.throws(() => validateExport(html, entry));
  }
});

test('an undrawn diagram is accepted only when declared unavailable and noted', () => {
  const drawn = '<section class="view-cell"><div class="view-body"><img src="data:image/svg+xml,x"></div></section>';
  const noted = '<section class="view-cell"><div class="note-line" data-tone="red">No drawing: failed</div></section>';
  const html = `<p>abc · Saved results, shown as recorded.</p>${drawn}${noted}`;
  const entry = errors => ({snapshot: {sha256: 'abc', project_claims: [], views: [{}, {}]}, diagram_errors: errors});
  assert.doesNotThrow(() => validateExport(html, entry(['1:9'])));
  assert.throws(() => validateExport(html, entry([])), /Diagram has no drawing/);
  assert.throws(() => validateExport(`<p>abc · Saved results, shown as recorded.</p>${drawn}<section class="view-cell"></section>`, entry(['1:9'])), /no note/);
});

test('gallery links survive a repository Pages prefix and escape notebook titles', () => {
  const html = galleryIndex({repository: 'owner/examples', revision: 'a'.repeat(40)}, [
    {html: 'basics/Test.html', title: '<img src=x>', source_url: 'https://github.com/owner/examples/blob/a/Test.lean'},
  ]);
  assert.ok(html.includes('href="basics/Test.html"'));
  assert.ok(html.includes('&lt;img src=x&gt;'));
  assert.ok(!html.includes('src=x>'));
  const dom = new JSDOM(html);
  try {
    const links = dom.window.document.querySelectorAll('.topic li a');
    assert.equal(links.length, 1);
    assert.equal(links[0].getAttribute('href'), 'basics/Test.html');
    assert.equal(links[0].textContent, '<img src=x>');
  } finally { dom.window.close(); }
});

test('known notebook cross-links survive export without rewriting external URLs', () => {
  const dom = new JSDOM('<a href="/?reference=ThreeState">Next</a><a href="https://other.invalid/?reference=ThreeState">External</a>');
  try {
    rewriteReferences(dom.window.document.body, [{snapshot: {file: 'ThreeState.lean'}, html: 'basics/ThreeState.html'}]);
    const links = dom.window.document.querySelectorAll('a');
    assert.equal(links[0].href, 'https://gallery.invalid/basics/ThreeState.html');
    assert.equal(links[1].href, 'https://other.invalid/?reference=ThreeState');
  } finally { dom.window.close(); }
});

test('notebook navigation preserves gallery and exact source links without changing content', () => {
  const dom = new JSDOM('<!doctype html><html><head></head><body><div class="app"><h1>Example</h1><p id="cell-first">Recorded claim</p></div></body></html>');
  const source = `https://github.com/owner/examples/blob/${'a'.repeat(40)}/examples/basics/A%22B.lean`;
  try {
    addNotebookNavigation(dom.window.document, {source_url: source, snapshot: {file: 'A"B.lean'}});
    const links = dom.window.document.querySelectorAll('.app > .gallery-nav a');
    assert.equal(links.length, 2);
    assert.equal(dom.window.document.documentElement.dataset.theme, 'light');
    assert.equal(dom.window.document.documentElement.style.colorScheme, 'light');
    assert.equal(links[0].getAttribute('href'), '../index.html');
    assert.equal(links[1].getAttribute('href'), source);
    assert.equal(links[1].getAttribute('title'), 'View A"B.lean on GitHub');
    assert.equal(dom.window.document.querySelector('h1').textContent, 'Example');
    assert.equal(dom.window.document.getElementById('cell-first').textContent, 'Recorded claim');
    assert.equal(dom.window.document.querySelectorAll('script').length, 0);
  } finally { dom.window.close(); }
});


test('gallery provides related-product navigation without losing notebook entry points', () => {
  const html = galleryIndex({repository: 'owner/examples', revision: 'a'.repeat(40)}, []);
  const dom = new JSDOM(html);
  try {
    const doc = dom.window.document;
    assert.ok(doc.querySelector('nav[aria-label="Main navigation"] a[href="https://glitnir.gimlelabs.com/"]'));
    assert.ok(doc.querySelector('a[href="https://gimlelabs.com/"]'));
    assert.ok(doc.querySelector('a.start[href="basics/ScalarDecay.html"]'));
    const feature = doc.querySelector('.triptych');
    assert.equal(feature.querySelector('h2').textContent, 'One model. Three honest outcomes.');
    assert.equal(feature.querySelectorAll('.verdict').length, 3);
    assert.ok(feature.querySelector('a[href="dynamics/Lorenz.html"]'));
    assert.ok(feature.querySelector('a[href="galerkin/NS_T3.html"]'));
    assert.equal(feature.querySelector('video source').getAttribute('src'), 'assets/triptych.webm');
    const captions = feature.querySelector('video track[kind="captions"]');
    assert.equal(captions.getAttribute('src'), 'assets/triptych.vtt');
    assert.equal(captions.hasAttribute('default'), false);
    assert.ok(feature.querySelector('a[href="receipts/proved-refuted-unknown.json"]'));
    assert.ok(doc.querySelector('nav[aria-label="Topics"] a[href="#pdes"]'));
    assert.ok(doc.querySelector('link[rel="icon"][href="assets/favicon.svg"]'));
    assert.equal(doc.querySelectorAll('h1').length, 1);
    assert.equal(doc.querySelector('h1').textContent, 'Glitnir notebooks.');
    assert.ok(doc.querySelector('.intro-note').textContent.includes('Lean, Mathlib, Forseti and Asgard'));
    assert.equal(doc.querySelectorAll('script').length, 0);
  } finally { dom.window.close(); }
});

test('gallery packages its local fonts, marks and font license for offline hosting', async () => {
  const fs = require('node:fs/promises');
  const os = require('node:os');
  const path = require('node:path');
  const output = await fs.mkdtemp(path.join(os.tmpdir(), 'forseti-gallery-assets-'));
  try {
    await copyGalleryAssets(output);
    for (const asset of ['gimle.svg', 'favicon.svg', 'inter-regular.ttf', 'inter-medium.ttf', 'LICENSE-Inter.txt', 'triptych-poster.svg', 'triptych.vtt', 'triptych.webm']) {
      const source = await fs.readFile(path.join(__dirname, '../gallery/assets', asset));
      assert.deepEqual(await fs.readFile(path.join(output, 'assets', asset)), source);
    }
    const transcript = await fs.readFile(path.join(output, 'triptych-transcript.html'), 'utf8');
    assert.match(transcript, /finite simulation.*does not prove/i);
    const receipt = await fs.readFile(path.join(output, 'receipts/proved-refuted-unknown.json'));
    assert.deepEqual(receipt, await fs.readFile(path.join(__dirname, '../releases/proved-refuted-unknown.json')));
  } finally { await fs.rm(output, {recursive: true, force: true}); }
});

test('the renderer scripts are the ones its page lists, in page order', () => {
  // Glitnir 0.1.9 ships one workbench script; later releases list several. The gallery
  // must not name them: it loads whatever `index.html` loads, in that order.
  const pages = [
    ['<script src="/katex/katex.min.js"></script>\n<script src="/export.js"></script>\n<script src="/circuits.js"></script>\n<script src="/cards.js"></script>\n<script src="/app.js"></script>',
      ['katex/katex.min.js', 'export.js', 'circuits.js', 'cards.js', 'app.js']],
    ['<script src="/katex/katex.min.js"></script>\n<script src="/export.js"></script>\n<script src="/circuits.js"></script>\n<script src="/cards.js"></script>\n<!-- host scripts -->\n<script src="/workbench.js"></script>\n<script src="/figures.js"></script>\n<script src="/chrome.js"></script>',
      ['katex/katex.min.js', 'export.js', 'circuits.js', 'cards.js', 'workbench.js', 'figures.js', 'chrome.js']],
  ];
  for (const [tags, expected] of pages) {
    const media = mkdtempSync(path.join(os.tmpdir(), 'gallery-media-'));
    writeFileSync(path.join(media, 'index.html'), `<!doctype html><html><head></head><body><div class="app"></div>\n${tags}\n</body></html>`);
    assert.deepEqual(rendererScripts(media), expected);
  }
});

test('a walkthrough export must say it is unchecked and never shown as recorded', () => {
  const notice = 'Unchecked walkthrough. Its claims restate theorems of o/r (p) at commit abcdef0; this page shows no checking result.';
  const entry = {walkthrough: {name: 'eth', map: 'walkthroughs/eth/map.html'}, snapshot: {sha256: 'abc', project_claims: [], views: [], preview: {notice}}};
  const html = `<p class="snapshot">abc. ${notice} This static page does not check or update results.</p>`;
  assert.doesNotThrow(() => validateExport(html, entry));
  assert.throws(() => validateExport('<p>abc · Saved results, shown as recorded.</p>', entry), /unchecked/);
  assert.throws(() => validateExport(`${html}<p>Saved results, shown as recorded</p>`, entry), /no saved results/);
});

test('walkthrough pages link back two levels and to their map beside them', () => {
  const dom = new JSDOM('<!doctype html><html><head></head><body><div class="app"><h1>Walkthrough</h1></div></body></html>');
  const source = `https://github.com/owner/examples/blob/${'a'.repeat(40)}/walkthroughs/eth/EthWalkthrough.lean`;
  try {
    addNotebookNavigation(dom.window.document, {html: 'walkthroughs/eth/EthWalkthrough.html', source_url: source,
      snapshot: {file: 'EthWalkthrough.lean'}, walkthrough: {name: 'eth', map: 'walkthroughs/eth/map.html'}});
    const links = [...dom.window.document.querySelectorAll('.app > .gallery-nav a')].map(link => link.getAttribute('href'));
    assert.deepEqual(links, ['../../index.html', 'map.html', source]);
  } finally { dom.window.close(); }
});

test('Markdown links to other sites become links outside code and mathematics', () => {
  const dom = new JSDOM('<main><p>See [`LICENSE`](https://example.invalid/LICENSE) and [the index](https://example.invalid/i#L3)\'s entry.</p><p><code>[x](https://example.invalid/c)</code> <span class="math">[y](https://example.invalid/m)</span> [z](map.html)</p></main>');
  try {
    const doc = dom.window.document;
    linkMarkdown(doc, doc.querySelector('main'));
    const links = [...doc.querySelectorAll('a')];
    assert.deepEqual(links.map(link => link.getAttribute('href')), ['https://example.invalid/LICENSE', 'https://example.invalid/i#L3']);
    assert.equal(links[0].innerHTML, '<code>LICENSE</code>');
    assert.equal(links[1].textContent, 'the index');
    assert.equal(doc.querySelector('p').textContent, "See LICENSE and the index's entry.");
    assert.ok(doc.body.textContent.includes('[x](https://example.invalid/c)'));
    assert.ok(doc.body.textContent.includes('[y](https://example.invalid/m)'));
    assert.ok(doc.body.textContent.includes('[z](map.html)'));
  } finally { dom.window.close(); }
});

test('the gallery index lists walkthroughs in their own section with their maps', () => {
  const html = galleryIndex({repository: 'owner/examples', revision: 'a'.repeat(40)}, [
    {html: 'basics/Test.html', title: 'Test'},
    {html: 'walkthroughs/eth/EthWalkthrough.html', title: 'ETH <walkthrough>', walkthrough: {name: 'eth', map: 'walkthroughs/eth/map.html'}},
  ]);
  const dom = new JSDOM(html);
  try {
    const doc = dom.window.document;
    const section = doc.getElementById('walkthroughs');
    assert.equal(section.querySelector('h2').textContent, 'Walkthroughs of existing formalizations');
    assert.ok(section.querySelector('header p').textContent.includes('Unchecked'));
    const title = section.querySelector('a.notebook-title');
    assert.equal(title.getAttribute('href'), 'walkthroughs/eth/EthWalkthrough.html');
    assert.equal(title.textContent, 'ETH <walkthrough>');
    assert.equal(section.querySelector('li p').textContent, WALKTHROUGHS.eth);
    assert.equal(section.querySelector('a.walkthrough-map').getAttribute('href'), 'walkthroughs/eth/map.html');
    assert.equal(doc.querySelectorAll('.topic:not(.walkthroughs) a[href^="walkthroughs/"]').length, 0);
    assert.ok(doc.querySelector('nav[aria-label="Topics"] a[href="#walkthroughs"]'));
    assert.equal(doc.querySelectorAll('.notebook-title').length, 2);
  } finally { dom.window.close(); }
});

test('the gallery index has no walkthrough section when none was exported', () => {
  const dom = new JSDOM(galleryIndex({repository: 'owner/examples', revision: 'a'.repeat(40)}, [{html: 'basics/Test.html', title: 'Test'}]));
  try {
    const doc = dom.window.document;
    assert.equal(doc.getElementById('walkthroughs'), null);
    assert.equal(doc.querySelector('nav[aria-label="Topics"] a[href="#walkthroughs"]'), null);
    assert.ok(doc.querySelector('nav[aria-label="Topics"] a[href="#pdes"]'));
    assert.ok(!doc.documentElement.outerHTML.includes('{{'));
  } finally { dom.window.close(); }
});


test('every published notebook has a description and every topic has navigation', () => {
  const {readdirSync} = require('node:fs');
  const entries = readdirSync(path.join(__dirname, '../examples'), {withFileTypes: true})
    .filter(item => item.isDirectory()).flatMap(item =>
      readdirSync(path.join(__dirname, '../examples', item.name))
        .filter(file => file.endsWith('.lean'))
        .map(file => ({html: `${item.name}/${file.replace('.lean', '.html')}`, title: file})));
  const dom = new JSDOM(galleryIndex({repository: 'owner/examples', revision: 'abc'}, entries));
  try {
    const d = dom.window.document;
    for (const item of d.querySelectorAll('.topic li')) {
      assert.ok(item.querySelector('p')?.textContent.length > 30, item.textContent);
    }
    for (const topic of d.querySelectorAll('.topic')) {
      assert.ok(d.querySelector(`.catalog nav a[href="#${topic.id}"]`), topic.id);
    }
  } finally { dom.window.close(); }
});
