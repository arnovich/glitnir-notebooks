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
