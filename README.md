# Glitnir notebooks

Worked mathematical notebooks in Lean, presented with [Glitnir](https://glitnir.gimlelabs.com/).
Explore circuits, dynamical systems, finance and partial differential equations
through readable explanations, models and proofs. The collection includes Lean
and Mathlib examples alongside notebooks using the
[Forseti](https://github.com/arnovich/forseti-lean) proof libraries and
[Asgard](https://github.com/arnovich/asgard-lean) circuit models.

Each notebook is an ordinary `.lean` file, with Markdown prose in Lean comments.
Read it in the gallery, or open it in Glitnir to inspect its source and check its
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

The best experience is to use [Glitnir](https://github.com/arnovich/glitnir) with VS Code
and Lean for VS Code, on local macOS or Linux. These steps use the
[current Glitnir release](https://github.com/arnovich/glitnir/releases/latest).

1. [Install VS Code](https://code.visualstudio.com/docs/getstarted/overview#install-vs-code),
   Python 3.12 or newer and [uv](https://docs.astral.sh/uv/getting-started/installation/).
2. [Install the Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
   and complete its setup guide, which installs elan and the Lean toolchain.
3. Install **Glitnir — Lean Notebooks** from the
   [Visual Studio Marketplace](https://marketplace.visualstudio.com/items?itemName=gimle.glitnir):
   search for it in the Extensions view, or run `code --install-extension gimle.glitnir`.
4. Clone this repository and build its Lean project once, from the repository root:

   ```sh
   lake exe cache get && lake build
   ```

   The first command downloads the prebuilt Mathlib files; the second builds
   Forseti, Asgard and the notebooks. With less than about 32 GB of memory,
   first build the AntitheticFeedback notebook's certificate imports one at a
   time, since Lake would start them together:

   ```sh
   for module in AIFSafety.MeshGeometry AIFSafety.MeshBin{0..7} \
       AIFSafety.CandidateMesh AIFSafety.Cell AIFSafety.Cells.Bin3.Slab100 \
       Gimle.Forseti.Examples.AIFCertifiedCellData; do
     lake build "$module"
   done
   ```
5. Open the folder in VS Code and a Lean file in a trusted workspace. Run
   **Glitnir: Set Up Environment → Set Up**, which downloads, verifies and installs
   Glitnir's backend in one step.
6. Install the Forseti plugin, which draws the diagrams and provides the
   evidence and decision cards: run **Glitnir: Install Extension Package… →
   Forseti → Download from this release**, and answer yes to `z3` if you want to
   run decisions.
7. Open [ScalarDecay.lean](examples/basics/ScalarDecay.lean), run
   **Glitnir: Open in Glitnir**, then try [ThreeState](examples/basics/ThreeState.lean).
   Each notebook's saved check results are in `<Notebook>.glitnir.json` beside it;
   **Check saved file** checks it again.

For coding-agent assistance, run **Glitnir: Set Up Coding Agent**, select this
workspace and your agent, and install the bundled `glitnir-notebooks` skill.
Start a new agent session and ask it to use that skill. See
[Glitnir's agent setup](https://github.com/arnovich/glitnir#coding-agents) for details.

**Note:** Plan for several GB of free disk space: the Mathlib files and the
project build take several GB, and Glitnir keeps copies of the toolchain and
compiled imports it checks against in its own artifact store in your user cache
(`glitnir/artifacts`; delete it at any time to free the space). Full builds and
checks also need substantial memory; a measured K5 build used about 10 GB of RAM
in one process, and AntitheticFeedback's imports include eight mesh modules of
4.3 to 4.5 GB each, a mesh geometry module of about 5.9 GB and two certificate
cells of about 7 GB. The first check of a
notebook replays Mathlib and Forseti once, which takes about 18 minutes on a
laptop; later checks take a few minutes.

## Examples

| Notebooks | Explore |
| --- | --- |
| [ScalarDecay](examples/basics/ScalarDecay.lean), [ThreeState](examples/basics/ThreeState.lean) | Basic claims, decisions and simulation |
| [AntitheticFeedback](examples/biochemistry/AntitheticFeedback.lean) | A biochemical controller that never overshoots by more than 60%: one certified cell checked, the full proof cited |
| [CircuitProofs](examples/circuits/CircuitProofs.lean), [EnergyOptimization](examples/circuits/EnergyOptimization.lean) | Circuit contracts and rewrites |
| [Fibonacci](examples/circuits/LinearCircuitFibonacci.lean), [Jordan](examples/circuits/LinearCircuitJordan.lean) | Discrete linear circuits |
| [Lorenz](examples/dynamics/Lorenz.lean) | Continuous trajectories and bounds |
| [HedgedSpread](examples/finance/HedgedSpread.lean), [HedgedSpreadRisk](examples/finance/HedgedSpreadRisk.lean), [RobustHedge](examples/finance/RobustHedge.lean) | A hedged book under every shock in a band, bounds on the odds of its stop under random shocks marked daily, and a hedge that covers an option on every path within a daily move band |
| [Laminar](examples/galerkin/NS_Laminar.lean), [T3](examples/galerkin/NS_T3.lean), [K5](examples/galerkin/NS_K5.lean), [B2](examples/galerkin/NS_B2.lean) | Finite-dimensional fluid models, energy and enstrophy |
| [Burgers](examples/pdes/Burgers.lean), [BurgersFronts](examples/pdes/BurgersFronts.lean), [Euler](examples/pdes/Euler.lean), [NavierStokes](examples/pdes/NavierStokes.lean) | Stream and PDE contracts |

The AntitheticFeedback notebook checks the circuit, the composition rule and one
cell of a certified proof, and cites the rest. The full certificate (2,960 cells
and the theorem they assemble into) is the opt-in `AIFSafety` library under
[`certificates/`](certificates/). It is not a default target: `lake build
AIFSafety` takes about 30 hours of processor time, and each cell needs over
7 GB of memory, so build it in chunks, running no more modules at once than you
have about 8 GB of memory for.

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
