# Glitnir notebook gallery design

## Intent

Make the gallery feel related to https://glitnir.gimlelabs.com while retaining
its topic catalog, real notebook previews and direct entry into the mathematics.
Use the frontend-design skill and existing Glitnir implementation as references.

## Design

Palette: white #ffffff, ink #15171a, muted #526174, blue #0066cc,
pale blue #f1f6fc and rules #dce5ef. Use locally hosted Inter regular/medium
for the gallery, and keep actual code/math in the canonical notebook renderer.
Use a shared Gimle mark, spacious left-aligned heading, split introduction/actions,
real preview images, and light topic rules. Keep the catalog central and readable.

Compared with the Glitnir landing page, this is a library rather than a product
pitch. Use "Glitnir notebooks" for the visitor-facing title, with the current collection
explicitly described as examples using Lean, Mathlib, Forseti and Asgard. Keep its concrete
subject description; avoid
adding feature marketing, signup, or decorative screenshots. Topic navigation
becomes a wrapping row on mobile; all assets remain local and Pages-prefix safe.

## Scope

- Gallery index, stylesheet and bundled brand/font assets.
- Copy those assets in the existing gallery exporter.
- Match the notebook navigation bar's color/spacing to the gallery.
- Preserve all notebook sources, results, Lean pins and Glitnir renderer behavior.

## Validation

- [x] Add asset-copy and gallery navigation regression checks, observe failure.
- [x] Implement the design and pass Node/Python tests and bundle guards.
- [ ] Build/check the gallery with existing pinned workflow.
- [x] Verify desktop, 390px and 320px rendering and offline assets.
- [x] Review with design, accessibility and export-correctness judges.
- [ ] Commit exact paths, open PR, and verify publication after checks.


## Verification and panel findings

Local checks: 45 Python tests, 7 Node tests, all 17 notebook bundles validated
structurally, and offline browser checks at 1100px, 390px and 320px. Local visual
preview uses the current successful main-branch gallery artifact, with the updated
index, assets and navigation styling. The complete pinned export runs in CI.

Design, accessibility and export-correctness judges found no blockers. Retained
the mobile Notebooks shortcut (the related-product link remains in the footer)
and extended browser checks to catch missing gallery images and failed fonts.
The export still uses Glitnir's canonical renderer and saved observations.

Assets reuse the existing Gimle mark and Inter fonts from the Glitnir landing
page; the Inter license is bundled in gallery/assets/LICENSE-Inter.txt.

## November 14 polish

Add a short reading description for each of the 19 example notebooks and the
missing Biochemistry navigation link. Keep notebook HTML and generated maps
light under a dark system preference. Fix the canonical Glitnir exporters too,
and pin the map helper to the reviewed source. Preserve saved notebook results.

Review caught and corrected the scope of ScalarDecay and HedgedSpread. All 21 pages from latest main, including RobustHedge and both walkthroughs,
passed offline desktop/mobile browser checks under a dark system preference.
All 14 JavaScript tests and 135 Python tests passed without skips; the 19
notebook bundles and both walkthrough originals validated. The guide rewrite
and shared exporter are in https://github.com/arnovich/glitnir/pull/108.
