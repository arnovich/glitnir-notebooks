// Open the complete site in a real browser with scripts disabled and no network.
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
const {pathToFileURL} = require('node:url');
const {chromium} = require('playwright');

// A walkthrough's map is the helper's page, published as drawn: it runs a script
// and loads KaTeX from cdnjs with Subresource Integrity. Load it
// with scripts on and the network blocked, show one statement, and fail on any
// script error or on a request to anything but that KaTeX.
const MAP_KATEX = /^https:\/\/cdnjs\.cloudflare\.com\/ajax\/libs\/KaTeX\/0\.16\.9\//;
async function checkMap(browser, file) {
  const context = await browser.newContext({colorScheme: 'dark', viewport: {width: 1100, height: 760}});
  const requests = [];
  const errors = [];
  await context.route(/^https?:/, route => { requests.push(route.request().url()); return route.abort(); });
  try {
    const page = await context.newPage();
    page.on('pageerror', error => errors.push(error));
    await page.goto(pathToFileURL(file).href);
    assert.equal(await page.locator('body').evaluate(node => getComputedStyle(node).backgroundColor), 'rgb(246, 247, 249)', `Map must stay light: ${file}`);
    const box = page.locator('#map [data-id]').first();
    const id = await box.getAttribute('data-id');
    await box.click();
    const data = JSON.parse(await page.locator('#walkthrough-data').textContent());
    assert.equal(await page.locator('#detail h1').textContent(), data.nodes.find(node => node.id === id).label, `Map does not show a statement: ${file}`);
    assert.deepEqual(errors, [], `Script error in ${file}`);
    assert.deepEqual(requests.filter(url => !MAP_KATEX.test(url)), [], `Map requests more than KaTeX: ${file}`);
  } finally { await context.close(); }
}

async function main() {
  const root = path.resolve(process.argv[2] || '_site');
  const manifest = JSON.parse(await fs.readFile(path.join(root, 'manifest.json'), 'utf8'));
  const browser = await chromium.launch({executablePath: process.env.GALLERY_CHROMIUM_EXECUTABLE || undefined});
  const context = await browser.newContext({javaScriptEnabled: false, colorScheme: 'dark', viewport: {width: 1100, height: 760}, deviceScaleFactor: 1});
  const network = [];
  await context.route(/^https?:/, route => { network.push(route.request().url()); return route.abort(); });
  const page = await context.newPage();
  await fs.mkdir(path.join(root, 'previews'), {recursive: true});
  try {
    for (const entry of manifest.notebooks) {
      await page.goto(pathToFileURL(path.join(root, entry.html)).href);
      assert.equal(await page.locator('h1').first().textContent(), entry.title);
      assert.equal(await page.locator('.app').evaluate(node => getComputedStyle(node).backgroundColor), 'rgb(255, 255, 255)', `Export must stay light with a dark system theme: ${entry.html}`);
      assert.equal(await page.locator('.view-cell').count(), entry.diagrams);
      const drawn = await page.locator('.view-cell').evaluateAll(views => views.filter(view => view.querySelector('svg.circuit-scene, .view-body img')).length);
      assert.equal(drawn, entry.diagrams - (entry.unavailable_diagrams || 0), `Undrawn diagrams: ${entry.html}`);
      assert.equal(await page.locator('.claim').count(), entry.claims);
      assert.equal(await page.locator('.katex-error,.view-wait,script').count(), 0);
      assert.ok(await page.locator('body').innerText().then(text => text.includes(entry.source_sha256)));
      if (entry.walkthrough) {
        // Unchecked: the page says so and links its clickable map, published beside it.
        assert.ok((await page.locator('.snapshot').innerText()).includes(entry.unchecked_notice), `Walkthrough not shown as unchecked: ${entry.html}`);
        await checkMap(browser, path.join(root, entry.walkthrough.map));
      }
      const imagesOK = await page.locator('img').evaluateAll(images => images.every(image => image.complete && image.naturalWidth > 0));
      assert.ok(imagesOK, `Unloaded images: ${entry.html}`);
      for (const href of await page.locator('a[href]').evaluateAll(links => links.map(link => link.getAttribute('href')))) {
        if (!/^(https?:|mailto:|#)/.test(href)) await fs.access(path.resolve(root, path.dirname(entry.html), href.split('#')[0]));
      }
      if (['basics/ThreeState.html', 'circuits/CircuitProofs.html'].includes(entry.html)) {
        await page.locator('.view-cell').first().scrollIntoViewIfNeeded();
        await page.screenshot({path: path.join(root, 'previews', path.basename(entry.html, '.html') + '.png')});
      }
      console.log(`Browser checked ${entry.html}`);
    }
    for (const width of [1100, 390, 320]) {
      await page.setViewportSize({width, height: 850});
      await page.goto(pathToFileURL(path.join(root, 'index.html')).href);
      assert.equal(await page.locator('.notebook-title').count(), manifest.notebooks.length);
      if (width === 1100) {
        const video = page.locator('.triptych video');
        assert.equal(await video.count(), 1, 'Opening demonstration video is missing');
        const mediaPaths = await video.evaluate(element => ({
          poster: element.getAttribute('poster'),
          source: element.querySelector('source')?.getAttribute('src'),
          captions: element.querySelector('track[kind="captions"]')?.getAttribute('src'),
        }));
        assert.deepEqual(mediaPaths, {
          poster: 'assets/triptych-poster.svg',
          source: 'assets/triptych.webm',
          captions: 'assets/triptych.vtt',
        });
        await Promise.all(Object.values(mediaPaths).map(relative => fs.access(path.join(root, relative))));
        const metadata = await video.evaluate(async element => {
          if (element.readyState < HTMLMediaElement.HAVE_METADATA) {
            await new Promise((resolve, reject) => {
              const timeout = setTimeout(() => reject(new Error('Timed out loading video metadata')), 10000);
              element.addEventListener('loadedmetadata', () => { clearTimeout(timeout); resolve(); }, {once: true});
              element.addEventListener('error', () => { clearTimeout(timeout); reject(new Error('Browser could not decode the opening video')); }, {once: true});
              element.load();
            });
          }
          return {
            width: element.videoWidth,
            height: element.videoHeight,
            duration: element.duration,
            vp9: element.canPlayType('video/webm; codecs="vp9"'),
          };
        });
        assert.equal(metadata.width, 1280);
        assert.equal(metadata.height, 720);
        assert.ok(metadata.duration >= 40 && metadata.duration <= 42, `Unexpected video duration: ${metadata.duration}`);
        assert.ok(metadata.vp9, 'Browser does not report VP9 playback support');
      }
      const galleryImagesOK = await page.locator('img').evaluateAll(images => images.every(image => image.complete && image.naturalWidth > 0));
      assert.ok(galleryImagesOK, 'Gallery image failed to load');
      const fontsOK = await page.evaluate(async () => {
        await document.fonts.ready;
        return ['400 17px Inter', '500 17px Inter'].every(font => document.fonts.check(font));
      });
      assert.ok(fontsOK, 'Gallery fonts failed to load');
      assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), 'Gallery overflows viewport');
      for (const href of await page.locator('a[href]').evaluateAll(links => links.map(link => link.getAttribute('href')))) {
        if (!/^(https?:|#)/.test(href)) await fs.access(path.join(root, href.split('#')[0]));
      }
      if (process.env.GALLERY_QA_DIRECTORY) {
        await fs.mkdir(process.env.GALLERY_QA_DIRECTORY, {recursive: true});
        await page.screenshot({path: path.join(process.env.GALLERY_QA_DIRECTORY, `gallery-${width}.png`), fullPage: true});
      }
    }
    assert.deepEqual(network, [], 'Exports must be readable offline');
  } finally { await browser.close(); }
}

main().catch(error => { console.error(error); process.exitCode = 1; });
