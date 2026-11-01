# Rechecking curated decision blocks

`python -m scripts.recheck` refreshes an accepted decision's generated theorem
in its original location. It retains prose, docstrings, shared definition
namespaces, their `open` commands, identity-check examples and surrounding text.
This fixes the source loss reported in [Glitnir #91](https://github.com/arnovich/glitnir/issues/91).
The editor's **Accept** inserts a candidate; the script owns this replacement.

The fresh candidate's supporting definitions must match the retained local
definitions or an explicitly opened `DecidedShared_*` namespace. The matching
is conservative and literal values are significant. Changed definitions,
ambiguous/nested namespaces, unsupported syntax and proof comments that would
be lost cause refusal. The old source and previous decision receipt are restored
when the run still owns them; detected external changes are never overwritten.

Before accepting a refresh, Glitnir's kernel checker checks the exact preserved
block, including its shared prelude and identity examples. The script saves that
verified block through Glitnir's records API, so it is recognized as accepted.
The normal whole-notebook check still follows the decision and evidence runs.
A refusal is reported per notebook and needs manual reconciliation, not a forced
rewrite.

The parser uses the Lark version already pinned for the gallery. Install that
requirement before running the repository tests:

```sh
python3 -m pip install --require-hashes --only-binary=:all: -r scripts/gallery/requirements.txt
python3 -m unittest discover -s tests -v
python3 scripts/check_bundles.py
```

Regression coverage includes the three actual NS_T3 blocks, all twelve identity
examples and both folded prose sections, nested comments, string literals,
proof-to-refutation changes, rejected verification, receipt-save failure and
concurrent source edits. Tests of the real records API additionally run when
Glitnir is installed; the pure source-edit tests need no Lean or Glitnir.

## Bounded CI rechecks

The 2026-11-01 serial full recheck exceeded GitHub's six-hour limit after 16 of
18 notebooks. CI now expands the selected inventory into one job per notebook,
with at most four jobs in parallel, independent six-hour bounds and no
fail-fast cancellation. The selection job pins one published Glitnir tag for
all shards, so a release during the run cannot mix backend/plugin versions. Every selected notebook still runs decisions, evidence,
whole-notebook kernel replay and views. Each job uploads a separately named
`notebook-recheck-<name>` artifact; review their reports and patches individually.
No generated notebook patch is applied automatically.

Euler's generated `noncomputable def` declarations are supported and compared
including their modifier. When the generated theorem name changes (for example,
a positive admitted claim gains a checked `_refuted` theorem), the original
claim stays in place and the new theorem is added beside it. Later refreshes
replace only the matching theorem. This preserves existing references such as
EnergyOptimization's `#print axioms` and leaves admitted claims admitted. The
new theorem is checked in the complete retained context; a proof depending on
an admitted claim cannot acquire checked status.

Validation plan: regression tests for matrix coverage, exact Euler definitions,
outcome changes and repeated refreshes; full Python/bundle checks; independent
correctness, proof-authority and CI reviews; then all PR CI gates before merge.

Validation completed locally: 127 tests pass with Glitnir installed (two existing
walkthrough-helper skips); the minimal pinned-Lark environment passes with
those two plus two optional Glitnir API skips. Bundle validation passes for all
18 notebooks and 276 saved claims. Correctness, proof-authority and CI judges
found no remaining blockers after fixing the single-release pin across shards.
The real Linux kernel recheck remains a CI merge gate.
