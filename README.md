# Glitnir notebooks

Worked mathematical notebooks in Lean, presented with [Glitnir](https://glitnir.gimlelabs.com/).
Explore dynamical systems, linear algebra, finance and partial differential
equations through readable explanations and proofs.

Each notebook is an ordinary `.lean` file, with Markdown prose in Lean comments.
Read it in the gallery, or open it in Glitnir to inspect its source and recorded
claims. Saved observations are shown as recorded; simulations are evidence.

In the [notebook gallery](https://notebooks.gimlelabs.com/) you can see rendered HTML snapshots of all the examples without installing Lean or Glitnir.

Start with the gallery's **proved, refuted, unresolved** demonstration: one
Lorenz model, three exact questions, a captioned recording, and the complete
browser-readable receipts. The same triptych is repeated on a three-mode
coefficient ODE, with its Navier–Stokes PDE nonclaim stated explicitly.

| A model in motion | How circuits compose |
| --- | --- |
| [![ThreeState notebook preview](https://notebooks.gimlelabs.com/previews/ThreeState.png)](https://notebooks.gimlelabs.com/basics/ThreeState.html) | [![CircuitProofs notebook preview](https://notebooks.gimlelabs.com/previews/CircuitProofs.png)](https://notebooks.gimlelabs.com/circuits/CircuitProofs.html) |

## Getting started

Start with the [notebook gallery](https://notebooks.gimlelabs.com/). Its HTML
snapshots can be read without installing Lean or Glitnir. Saved results are
shown as recorded; viewing a page does not run a new proof check.

To read the source interactively, install
[Glitnir — Lean Notebooks](https://marketplace.visualstudio.com/items?itemName=gimle.glitnir)
and the Lean 4 extension in VS Code. See
[Glitnir's guide](https://github.com/arnovich/glitnir/blob/main/docs/guide.md)
for opening notebooks and understanding claim status.

**Three notebooks build with public dependencies.** ScalarDecay, Fibonacci and
Jordan live in the independent [`public/`](public/) Lake project, pinned to
[Atlas-lean](https://github.com/arnovich/atlas-lean). From that directory, run
`lake exe cache get` and `lake build`, then use Glitnir's **Check saved file**.
ScalarDecay intentionally includes one unproved claim. The Fibonacci and Jordan
notebooks prove matrix observation results, not compiled-circuit contracts.

The other 16 notebooks retain their existing sources and recorded results.
Their root Lake project still requires internal libraries, so a public checkout
cannot rebuild their checks, diagrams or simulations. Reusable mathematics is
being separated from those libraries before further migration to Atlas.
Automated Lean builds and rechecks cover the public project. The restricted
collection can be rechecked locally by a maintainer with access to its pinned
libraries; bundle validation still covers every saved snapshot.

The two walkthroughs below use separate public formalizations. They are
readable independently, but their Lean project templates remain untested and
the walkthroughs are explicitly unchecked.

For coding-agent assistance, see
[Glitnir's agent setup](https://github.com/arnovich/glitnir#coding-agents).

## Examples

| Notebooks | Explore |
| --- | --- |
| [ScalarDecay](public/examples/basics/ScalarDecay.lean), [ThreeState](examples/basics/ThreeState.lean) | Basic claims, decisions and simulation |
| [AntitheticFeedback](examples/biochemistry/AntitheticFeedback.lean) | A biochemical controller that never overshoots by more than 60%: one certified cell checked, the full proof cited |
| [CircuitProofs](examples/circuits/CircuitProofs.lean), [EnergyOptimization](examples/circuits/EnergyOptimization.lean) | Circuit contracts and rewrites |
| [Fibonacci](public/examples/circuits/LinearCircuitFibonacci.lean), [Jordan](public/examples/circuits/LinearCircuitJordan.lean) | Linear observations using Atlas |
| [Lorenz](examples/dynamics/Lorenz.lean) | Continuous trajectories and bounds |
| [HedgedSpread](examples/finance/HedgedSpread.lean), [HedgedSpreadRisk](examples/finance/HedgedSpreadRisk.lean), [RobustHedge](examples/finance/RobustHedge.lean) | A hedged book under every shock in a band, bounds on the odds of its stop under random shocks marked daily, and an at-the-money call hedged on every path whose daily moves stay in a band |
| [Laminar](examples/galerkin/NS_Laminar.lean), [T3](examples/galerkin/NS_T3.lean), [K5](examples/galerkin/NS_K5.lean), [B2](examples/galerkin/NS_B2.lean) | Finite-dimensional fluid models, energy and enstrophy |
| [Burgers](examples/pdes/Burgers.lean), [BurgersFronts](examples/pdes/BurgersFronts.lean), [Euler](examples/pdes/Euler.lean), [NavierStokes](examples/pdes/NavierStokes.lean) | Stream and PDE contracts |

The AntitheticFeedback notebook checks the circuit, the composition rule and one
cell of a certified proof, and cites the rest. The full certificate (2,960 cells
and the theorem they assemble into) is the `AIFSafety` library under
[`certificates/`](certificates/). Rebuilding it requires the internal dependencies described above and substantial
computing resources. See its README for details.

Each [gallery entry](https://notebooks.gimlelabs.com/) links
to its rendered notebook and exact Lean source revision.

## Walkthroughs

Guided readings of Lean formalizations by others, each with a clickable map of
how the proof fits together. They are **unchecked**: the projects use a Lean
version Glitnir does not check, so no claim has a checking result and nothing
was compiled. Each claim restates a theorem of the original word for word, and
a text check compares it with the original's source at the pinned commit.

| Walkthrough | Explains | Map |
| --- | --- | --- |
| [EthWalkthrough](walkthroughs/eth/EthWalkthrough.lean) | A $2^{o(n)}$-time algorithm for 3-SAT and the failure of ETH: the project [`eth`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth) of `anthropics/formal-math` | [map](walkthroughs/eth/map.html) |
| [ThreeSumApspWalkthrough](walkthroughs/3sum-apsp/ThreeSumApspWalkthrough.lean) | Truly subquadratic 3SUM and truly subcubic APSP: the project [`3sum-apsp`](https://github.com/anthropics/formal-math/tree/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp) of `anthropics/formal-math` | [map](walkthroughs/3sum-apsp/map.html) |

The formalizations and papers belong to their authors; see each walkthrough's
opening for attribution and licences.

This repository is maintained by its authors and does not accept external contributions.
Licensed under the [MIT License](LICENSE).


The ETH/3SAT walkthrough includes the first curated proof atlas in
`walkthroughs/eth/atlas.json`. With an atlas-capable Glitnir runtime, its Graph view
offers Reading-first and Map-first exploration of separate paper and Lean routes.
Its 18 arguments include a deeper Lean branch from improved pieces through the
padded-to-counted conversion to the padding-machine execution lemma. Route
overview and Used by expose shared steps; argument links work in the preview and
HTML export. The added source notes distinguish counted transitions from
Turing-machine time.
The formalization remains unchecked by Glitnir; the atlas grants no proof status.
Validate the sidecar with the installed notebook skill’s `scripts/proof_atlas.py`
against `walkthroughs/eth/outline.json`, in addition to the existing walkthrough checks.
