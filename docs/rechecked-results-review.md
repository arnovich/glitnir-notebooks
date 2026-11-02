# Review of the preserved recheck results

## Provenance and scope

The source artifacts are from [successful run 41358092974](https://github.com/arnovich/glitnir-notebooks/actions/runs/41358092974),
head `cfe80e4c8cfb1cc27dc35634a9521a12766d08ff`, merged by PR #26.
The selected runtime was the published Glitnir **v0.1.10**, as recorded in the
shard installation logs. All 18 notebook jobs reported `checked_snapshot`, no problems and no withheld
claims. Each notebook's source/results pair was taken only from its own
`notebook-recheck-<name>` artifact, and each patch was checked against the merged
baseline before application. Files from other notebooks bundled in that shard
were not imported. No proof/status metadata was edited by hand.

Import 16 saved-result updates and eight notebook source updates. Lorenz and
NS_T3 remain exactly as committed: `releases/proved-refuted-unknown.json` binds
their exact source/results bytes to the v0.1.10 triptych. Their new artifacts
add no claims, so preserving that receipt takes precedence over refreshing
checker fingerprints or equivalent normalization tactics.

Two prose corrections are prepared to distinguish ThreeState and
EnergyOptimization's admitted positive claims from their separately checked
negation theorems. They will be checked and recorded in CI before their final
source/results pairs are added to this PR; the imported pairs in this commit
remain exact existing CI artifacts.

## Evidence review

All 276 original claims retain their statuses and axiom sets. Seven additional
negation theorems are checked; the corpus has 283 saved claims. All eight
admitted claims remain admitted. The new negations use only the standard Lean
axioms, with no `sorryAx`. Simulation remains evidence, and unresolved decisions
remain unknown (Lorenz and NS_T3 exhausted their bounded searches; the
HedgedSpreadRisk request remains unsupported). Existing statements, supporting definitions, shared namespaces,
identity examples and comments are preserved in the generated patches. Only the
two status explanations above are the planned follow-up edits.

The existing theorem proof edits normalize rational casts with
`norm_num [Rat.mkRat_eq_div]`. The seven new theorems accompany false positive
claims in Burgers, BurgersFronts, EnergyOptimization, NS_B2, NS_K5, NS_Laminar
and ThreeState. Generated naming is retained, including
`front_band_refuted_refuted`: the directive itself is named `front_band_refuted`.

Saved check/environment and proposition hashes can change across checker
versions or environments without a statement change; proposition hashes bind
checker identity as well as the compiled canonical expression. These records
are observations of the recorded environment, not a claim that dependencies
remain unchanged in another checkout.

| Notebook | Original claims | Rechecked claims | Update |
| --- | ---: | ---: | --- |
| AntitheticFeedback | 11 | 11 | Import checked update |
| Burgers | 19 | 20 | Import checked update |
| BurgersFronts | 5 | 6 | Import checked update |
| CircuitProofs | 4 | 4 | Import checked update |
| EnergyOptimization | 10 | 11 | Import checked update |
| Euler | 29 | 29 | Import checked update |
| HedgedSpread | 11 | 11 | Import checked update |
| HedgedSpreadRisk | 12 | 12 | Import checked update |
| LinearCircuitFibonacci | 7 | 7 | Import checked update |
| LinearCircuitJordan | 11 | 11 | Import checked update |
| Lorenz | 5 | 5 | Retain v0.1.10 receipt |
| NS_B2 | 26 | 27 | Import checked update |
| NS_K5 | 35 | 36 | Import checked update |
| NS_Laminar | 26 | 27 | Import checked update |
| NS_T3 | 33 | 33 | Retain v0.1.10 receipt |
| NavierStokes | 17 | 17 | Import checked update |
| ScalarDecay | 4 | 4 | Import checked update |
| ThreeState | 11 | 12 | Import checked update |

## Validation

The exact CI artifact sources passed all 18 independent kernel rechecks.
Local validation: the 128-test Python suite passes with two existing
walkthrough-helper skips; all 13 gallery tests pass; bundle validation passes
for all 18 notebooks/283 claims; the six exact triptych receipts still pass;
`git diff --check` passes. The local Lean build and corrected-prose checks were
stopped at the owner's request to move the heavy validation to CI. They are not
reported as completed local checks.

The two corrected notebooks will be checked in a temporary CI authoring branch,
which applies only the reviewed prose patch before using the existing recheck
pipeline. Its generated source/results artifacts will be copied back together.
The PR's own editor, gallery and targeted recheck CI still need to pass before
merge.
