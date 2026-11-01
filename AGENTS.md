# Glitnir notebooks

For notebook authoring, use Glitnir's `glitnir-notebooks` skill. Install it with
**Glitnir: Set Up Coding Agent**, as described in [getting started](README.md#getting-started).

Keep notebook names unique and update the Lake configuration and README catalog
when adding or moving examples.

Run the repository checks with Python 3.12 or newer:

```sh
python3 -m unittest discover -s tests -v
python3 scripts/check_bundles.py
```

Every notebook needs a committed `<Notebook>.glitnir.json` whose recorded
source SHA-256 matches the saved notebook. The bundle check validates it with
Glitnir's record loader when the Glitnir backend is importable, otherwise
structurally. After rechecking notebooks in another checkout, copy their results
here with `python3 -m scripts.collect_results /path/to/that/checkout` (add
`--dry-run` to validate only), then commit each results file by its path.

To recheck notebooks, use the `Notebook recheck` workflow. On pull requests it
rechecks only what changed: `scripts/select_recheck.py` takes
`git diff --name-only <base>...HEAD` and selects the notebooks whose `.lean`
source changed plus those that import them (through `import` lines and the
lakefile's libraries). A change to `lean-toolchain`, `lake-manifest.json`,
`lakefile.toml`, the gallery or recheck requirements, `scripts/recheck.py`,
`scripts/select_recheck.py` or the workflow rechecks all; results files and
docs recheck nothing, and the workflow's `.lean` paths filter does not even
start it for a pull request without `.lean` changes. When nothing is selected
the job succeeds with a summary line and builds no Lean. Manual dispatch takes
an optional `only` list (empty means all), on Linux with the gallery's pinned
Glitnir. Because the diff is against the pull request's base, a results commit
on top of a source change rechecks that notebook again. `python -m scripts.recheck` checks each notebook
through Glitnir's preview service, decides out-of-date decisions again
(replacing an earlier decision's block the way **Accept** inserts it), runs
out-of-date evidence again and draws every view so its drawing is saved. The
workflow never pushes: it uploads the results, `recheck.patch` and a
per-notebook report (`report.md`, also the job summary) that lists every claim
whose status changed. Review the report, apply the patch and commit each file
by its path. Results saved on one machine read as out of date in another
checkout: Glitnir's environment fingerprint includes Lake traces that name
each locally built module's absolute source path. The gallery and the bundle
check compare the saved source only, so they are unaffected.

For Lean source or Lake configuration changes, also run `lake build`. Bundle
checks and editor builds do not replay notebook claims. Use Glitnir's installed
skill for checking and metadata handling; preserve pinned dependencies unless
an upgrade is intentional.

## Walkthroughs

`walkthroughs/<name>/` explains an existing Lean formalization that Glitnir
cannot check (another Lean version, another repository). Each folder holds one
notebook with a unique name (`<Name>Walkthrough.lean`), its `outline.json`,
`assets/` (figures and `map.svg`), `map.html`, `lean-toolchain` and a
`lakefile.toml` template that requires the original by Git at the outline's
commit. The template is untested and nothing builds it (Glitnir task 371).
Walkthroughs are **unchecked**: never compiled, never rechecked, and not part of
the root Lake project; do not add them to `lakefile.toml`, and never create a
`.glitnir.json` for one by hand. The bundle check and recheck ignore them, and
the walkthrough check and gallery build refuse a results file.

To add one, write it with the `glitnir-notebooks` skill's walkthrough workflow,
then copy it here: rename the notebook uniquely, set the outline's
`project.root` to `../_originals/<first 12 digits of the commit>/<repository
name>/<project path>` (also for `sources` paths into the original), make every
file of the original that the prose names a link to
`https://github.com/<owner>/<repo>/blob/<commit>/<project path>/<file>#L<line>`
(`tree/` for a folder), and draw the map with public links. Add its one-line
description to `WALKTHROUGHS` in `scripts/gallery/render.cjs` and a README row.

Fetch and check, with Python 3.12 or newer:

```sh
python3 scripts/fetch_originals.py
python3 scripts/check_walkthroughs.py
python3 walkthroughs/_originals/walkthrough-<commit>.py map walkthroughs/<name>/outline.json --links public --out walkthroughs/<name>
```

`fetch_originals.py` checks out each outline's repository (an `https://` URL;
`file://` only for the tests, under `WALKTHROUGH_ALLOW_FILE_REPOSITORIES=1`) at
its commit, once per distinct commit, under the git-ignored `walkthroughs/_originals/`, and
downloads Glitnir's walkthrough helper at the commit pinned with its SHA-256 in
`scripts/walkthrough-script.txt` (update both together when repinning).
`check_walkthroughs.py` verifies that hash, runs the helper's `check` with
`--notebook` (every claim and outline entry must match the original's source
as text) and requires `map.html` and `assets/map.svg` to be exactly what
`map --links public` draws, with no local path. CI runs both in the bundle and
gallery workflows; `REQUIRE_WALKTHROUGH_HELPER=1` makes the tests that need
the pinned helper fail rather than skip.

The gallery exports each walkthrough through Glitnir's `SavedNotebook` with no
results file, replaces its notice with an unchecked one (CI's text check runs
before publication), publishes `map.html` beside the page and lists
walkthroughs in their own index section. Glitnir's renderer shows Markdown
links to other sites as text; on walkthrough pages `render.cjs` turns them into
links after export.

Until Glitnir renders them (Glitnir task 383), walkthrough prose avoids the
Markdown Glitnir 0.1.9 shows as source text: TeX in headings (write headings in
plain text), `*italic*` and `_italic_` (quote defined terms, use **bold** for
emphasis and run-in labels), `*` and numbered lists (use `- `), and bold around
mathematics or code. Mathematics in paragraphs renders.

Known item: `map.html` loads KaTeX from cdnjs without Subresource Integrity.
The maps must stay byte-identical to the helper's output, so this is a Glitnir
follow-up. The gallery's browser check loads each map with scripts on and the
network blocked, and fails on a script error or on any other request.

## Certificate libraries

A notebook may cite a proof too large for a notebook check. Put it in an opt-in
library under `certificates/` (`srcDir = "certificates"`), never in
`defaultTargets`; it has no Glitnir results. When a notebook imports one of its
modules, prebuild that module's heavy imports one at a time in
`.github/workflows/check.yml` and the README's getting-started step;
`tests/test_certificates.py` checks the CI list against the notebook's imports.

## Gallery maintenance

The canonical repository is `arnovich/glitnir-notebooks`; the public gallery is
https://notebooks.gimlelabs.com/. Its custom domain is configured in GitHub Pages
and Cloudflare DNS, independently of the repository name.

The `Notebook gallery` workflow builds on main pushes, pull requests and manual
dispatch. It retains preview artifacts and deploys Pages only from public main.
To activate publication, set **Settings → Pages → Source → GitHub Actions** and
run the workflow. Restrict the `github-pages` environment to `main`. Keep README
gallery/image URLs on the stable custom domain; update repository and source
references if the repository name or owner changes.

The repository was formerly `arnovich/forseti-examples`. Do not recreate that
repository name: doing so removes GitHub's redirects to `glitnir-notebooks`.
Old GitHub Pages project paths are outside the repository-rename redirect
guarantee; use the canonical gallery domain.

The gallery uses the backend, renderer and Forseti view provider of the latest
published Glitnir release, or of the tag a workflow dispatch names, resolved by
`scripts/glitnir_release.py` and installed by hash from that release's SHA256SUMS. Use Python 3.12+,
Node 22.22.2, Lean 4.35.0 and a working sandbox (bubblewrap on Linux). Diagrams are
drawn in this project's own Lake environment, so first build the modules they
import, from this checkout:

```sh
python3.12 -m venv .venv
.venv/bin/python -m pip install --require-hashes --only-binary=:all: -r scripts/gallery/requirements.txt
lake exe cache get
lake build $(.venv/bin/python -m scripts.build_gallery --list-diagram-imports)
npm ci --ignore-scripts
npx playwright install chromium
npm test
.venv/bin/python -m scripts.build_gallery
npm run gallery:check -- _site
```

Use a new output directory; for another build, pass `--output /path/to/new-site`
and check that same directory. Keep generated HTML and previews uncommitted.
Exports go through Glitnir's static export (`SavedNotebook`) and its renderer's
Export HTML, from the committed sources and saved results; they check no claim,
run no evidence or decision, and write nothing beside the notebooks. Pages show
Glitnir's "Saved results, shown as recorded" state, and each results file must
be for that exact source. A diagram that cannot be drawn, or that Glitnir drew
while a dependency's state could not be read ("uncertain"), fails the build
and is not cached; `--allow-diagram-errors` shows a note instead, and `--only NAME`
exports a subset for local previews. Verify pages offline and at desktop and
mobile widths. Upgrade the pinned Python, Node and Lean export dependencies
together and verify all exports when changing the renderer.
