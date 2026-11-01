import Mathlib
import Gimle.Forseti.Examples.AIFCertifiedCell
import Gimle.Forseti.Examples.AIFCircuitBinding
import Gimle.Forseti.Examples.AIFSlabDrift
import AIFSafety.Cells.Bin3.Slab100

/-!
# Antithetic feedback never overshoots its reference by more than 60%

Antithetic integral feedback is a small chemical controller: two controller
species are produced at rates set by a reference and by the output, and they
annihilate each other on contact. The annihilation makes the controller
integrate the output's error, so whenever the loop settles, it settles exactly
at the reference, whatever the plant's rates are. Whether it settles, and how far
it overshoots on the way, depends on the rates. A controller
started from nothing has to push the output up from zero, and an integrator that
has wound up can carry it far past the reference before pulling it back. Whether
it does is a question about the whole trajectory, and a simulation answers it
only for the parameters and the time it was run.

This notebook is about one concrete circuit: four species, every rate constant
one, reference two, every species starting at zero,

$$ \dot x_1 = z_1 - x_1, \quad \dot x_2 = x_1 - x_2, \quad
   \dot z_1 = 2 - \eta z_1 z_2, \quad \dot z_2 = x_2 - \eta z_1 z_2, $$

with the annihilation rate $\eta$ fixed along each trajectory. Here $x_1$ and
$x_2$ are the plant, with $x_2$ the regulated output. $z_1$ is the actuator: it
is produced at the reference rate 2 and drives production of $x_1$. $z_2$ is the
sensor: it is produced in proportion to $x_2$. The two annihilate at rate
$\eta z_1 z_2$, and the set point is $x_2 = 2$. Time and concentrations are
dimensionless. The circuit Lean reasons about is the one Asgard compiles from
these named equations; the first claims below check that it equals them.

**Proved in the `AIFSafety` library, cited here and not checked by this
notebook.** For every fixed $\eta \in [8, 12]$ the
zero-start circuit has exactly one behaviour for $t \ge 0$, its four species
stay nonnegative, and its output satisfies $0 \le x_2(t) \le 16/5$ **for all
$t \ge 0$** — never more than 60% above the reference — and $x_2(t) \le 5/2$
from $t = 30$ on. The bound is not claimed to be the smallest one. The proof
covers the first thirty time units with a moving
tube around a numerically computed trajectory, cut into $8 \times 370 = 2960$
cells, each checked by the Lean kernel. At $t = 30$ the tube lies inside a
region where a quadratic Lyapunov function takes over for all later time.

**Checked here.** The library is far too large for a notebook check: Glitnir
replays every imported proof through the kernel, and the 2960 cells take about
30 hours of processor time. So this notebook checks the parts that carry the
argument:

- the compiled circuit has the equations above;
- for every fixed $\eta \ge 0$ a behaviour exists, is unique and stays
  nonnegative;
- the composition rule that turns one checked certificate per cell into a tube
  the trajectory cannot leave;
- every behaviour lies in the first cell's tube, from the start, for
  $\eta \in [8, 17/2]$, and that cell is the mesh's first cell;
- one cell of the 2960, checked from scratch.

The full statement is written out at the end as a Lean definition, and the
claim that the library proves it is made there, in prose, not as a checked
claim.

**Not claimed.** Anything about $\eta$ outside $[8, 12]$ or varying in time,
about other initial states, or about other rate constants or references: the
robustness antithetic feedback is known for is not what is proved here. Nor that
$x_2$ converges to the reference: the late-time result is the bound
$x_2 \le 5/2$, not convergence. Nothing
stochastic: these are the mass-action rate equations, not the chemical master
equation, and nothing here says how a small number of molecules behaves. The
numerically computed tube is untrusted input; only the kernel checks of each
cell make it evidence of anything.

## The circuit, as Lean reads it {fold}

The circuit is Asgard's `Gimle.Asgard.Examples.AIF`: a program of four named
equations, compiled to a typed circuit and closed into feedback. Its input
order is $\eta$ followed by the species $(x_1, x_2, z_1, z_2)$, and its
observation reads $x_2$.
-/

namespace Notebook.AntitheticFeedback
open Gimle.Asgard Gimle.Forseti.Examples

/-- The compiled field is the four rate equations. -/
theorem field_equations (eta : ℝ) (x : Point 4) :
    Gimle.Asgard.Examples.AIF.field.run (pointAppend ![eta] x) =
      ![x 2 - x 0, x 0 - x 1, 2 - eta * x 2 * x 3, x 1 - eta * x 2 * x 3] := by
  exact Gimle.Asgard.Examples.AIF.field_appended eta x

/-- A behaviour of the closed circuit is exactly a solution of the rate equations
from zero, for $t \ge 0$. -/
theorem realizes_iff (eta : ℝ) (state : Dynamics.Signal 4) :
    Gimle.Asgard.Examples.AIF.Realizes eta state ↔ state 0 = 0 ∧
      ∀ t ∈ Set.Ici (0 : ℝ), ∀ i,
        HasDerivWithinAt (fun s => state s i)
          (![state t 2 - state t 0, state t 0 - state t 1,
            2 - eta * state t 2 * state t 3,
            state t 1 - eta * state t 2 * state t 3] i) (Set.Ici 0) t := by
  exact Gimle.Asgard.Examples.AIF.realizes_iff eta state

/-- The observation is the second plant species. -/
theorem output_is_x2 (x : Point 4) : Gimle.Asgard.Examples.AIF.output.run x 0 = x 1 := by
  exact Gimle.Asgard.Examples.AIF.output_correct x

/-!
## One behaviour, and it stays nonnegative {fold}

Without a behaviour, a bound over all behaviours would hold vacuously; without
uniqueness, there would be no single trajectory to speak of. For every fixed $\eta \ge 0$ the
library constructs a global solution of the rate equations, proves that any
two behaviours agree for $t \ge 0$, and that every species stays nonnegative:
if one species is at zero while the others are nonnegative, its rate is
nonnegative (for $z_1$ it is 2), so no species can cross zero.
-/

/-- For every fixed $\eta \ge 0$ the zero-start circuit has a behaviour. -/
theorem exists_behaviour (eta : ℝ) (heta : 0 ≤ eta) :
    ∃ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state := by
  exact AIFCircuitBinding.exists_realization eta heta

/-- Any two behaviours agree for all $t \ge 0$. -/
theorem behaviour_unique (eta : ℝ) (heta : 0 ≤ eta) (x y : Dynamics.Signal 4)
    (hx : Gimle.Asgard.Examples.AIF.Realizes eta x)
    (hy : Gimle.Asgard.Examples.AIF.Realizes eta y) : Set.EqOn x y (Set.Ici 0) := by
  exact AIFCircuitBinding.realization_unique eta heta x y hx hy

/-- Every species of a behaviour is nonnegative for $t \ge 0$. -/
theorem species_nonnegative (eta : ℝ) (heta : 0 ≤ eta) (state : Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 4) : 0 ≤ state t i := by
  exact AIFCircuitBinding.realization_nonnegative eta heta state realized t ht i

/-!
## A tube the trajectory cannot leave {fold}

The upper bound comes from a tube. Shift the species so the equilibrium sits
at the origin, $y = (x_1 - 2, x_2 - 2, z_1 - 2, \eta z_2 - 1)$; the start is
then $(-2, -2, -2, -1)$. A numerical search proposes a moving center $c(t, \eta)$
and a moving positive-definite matrix $M(t, \eta)$, and the tube is the set of
states whose error $e = y - c$ has weighted squared distance
$e^\top M(t, \eta)\, e \le 1/40000$, called its energy below. The time span
$[0, 30]$ and the parameter range $[8, 12]$ are cut into a mesh of cells: 8
bins of $\eta$, of width $1/2$, and 370 time slabs, short at the start, where
the trajectory moves fastest, and longer later.

On each cell the center and matrix are cubic in time and linear in $\eta$, and
the tube is invariant if the energy's rate of change is negative whenever the
energy reaches the boundary. That drift is a matrix polynomial in $t$ and
$\eta$ over the cell. Written in a Bernstein basis, it suffices that every
Bernstein coefficient matrix be negative definite, and each is certified by
writing its negative as a weighted sum of squares. The bilinear term
$\eta z_1 z_2$ makes the drift depend on the error in $z_1$, which the tube
keeps within $\pm 3/200$, so the drift is checked at both ends. The kernel
recomputes the coefficients from the exact rational data and checks every
decomposition; the numerical search only proposed the data.

The rule below is the step from cells to the trajectory. Given a mesh whose
cells join continuously, a checked certificate for every cell of one $\eta$
bin, and a start inside the first cell's tube, every solution stays in the
tube on every cell. Nothing is assumed about the trajectory beyond its
equations.
-/

/-- The composition rule: one checked certificate per cell, and the start in the
first tube, keep a solution in the tube on every cell of the bin. -/
theorem tube_from_certificates {nt nb : Nat} (m : AIFMesh.Mesh (nt + 1) nb) (b : Fin nb)
    (widths : ∀ i, 0 < (m.slab b i).step)
    (eta_ordered : m.edges b.castSucc < m.edges b.succ)
    (p : ℝ) (hp : p ∈ Set.Icc (m.edges b.castSucc : ℝ) (m.edges b.succ : ℝ))
    (state : ℝ → Fin 4 → ℝ)
    (derivative : ∀ i : Fin (nt + 1),
      ∀ t ∈ Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ), ∀ j,
        HasDerivWithinAt (fun z => state z j) (AIFDriftModel.field p (state t) j)
          (Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ)) t)
    (certificates : ∀ i, AIFSlabDrift.CellCertificates (m.slab b i))
    (initial : AIFMesh.tubeEnergy (m.slab b 0) (m.times 0) p (state (m.times 0)) ≤ 1/40000) :
    ∀ i, ∀ t ∈ Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ),
      AIFMesh.tubeEnergy (m.slab b i) t p (state t) ≤ 1/40000 := by
  exact AIFSlabDrift.mesh_invariant_of_certificates m b widths eta_ordered p hp state
    derivative certificates initial

/-!
## The first cell, from the start {fold}

The first cell is $t \in [0, 1/200]$ with $\eta \in [8, 17/2]$. Its certificate
is checked in forseti-lean's `AIFCertifiedCellData`, which this notebook's
check replays with its other imports, and its slab is the candidate mesh's
cell $(0, 0)$, checked below. The start
$(-2, -2, -2, -1)$ is the tube's center at $t = 0$, energy zero. So every
behaviour of the circuit is inside the first tube on the first cell. The tube
bounds the shifted actuator $z_1$ to within $3/200$ of the center; it is not yet an output bound.
-/

/-- Every behaviour stays in the first cell's tube for $t \in [0, 1/200]$. -/
theorem first_cell (eta : ℝ) (heta : eta ∈ Set.Icc (8 : ℝ) (17/2))
    (state : Dynamics.Signal 4) (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/200)) :
    AIFMesh.tubeEnergy AIFCertifiedCellData.slab t eta
      (AIFPhysicalCoordinates.shift eta (state t)) ≤ 1/40000 := by
  have h0 : (0 : ℝ) ≤ eta := by linarith [heta.1]
  rw [AIFCircuitBinding.realization_unique eta h0 state _ realized
    (AIFCircuitBinding.solution_realizes eta h0) ht.1]
  exact AIFCertifiedCell.solution_in_tube eta heta t ht

/-- That cell's slab is cell $(0, 0)$ of the candidate mesh the library uses. -/
theorem first_cell_in_mesh :
    AIFCertifiedCellData.slab = AIFSafety.CandidateMesh.mesh.slab 0 0 := by
  decide +kernel

/-!
## One cell of the full mesh {fold}

The library's cells all have the same form. Here is one, rechecked by this
notebook from scratch: $\eta$ bin 3, $\eta \in [19/2, 10]$, and time slab 100,
$t \in [3, 31/10]$. Its slab is the candidate mesh's cell, read from the mesh
data itself. The kernel recomputes the drift tables at both ends of the $z_1$
error, checks their 80 square certificates, the containment margin and the
symmetry of the metric data, and an output margin: on this cell, inside the
tube, the shifted output satisfies $y_2 \le 6/5$ (Lean's index 1), which is
$x_2 \le 16/5$.
-/

/-- Cell (3, 100): the drift inequality holds throughout its tube. -/
theorem cell_drift :
    AIFSafety.Cell.Drift (AIFSafety.CandidateMesh.mesh.slab 3 100) := by
  exact AIFSafety.Cells.Bin3.Slab100.drift_in_mesh

/-- Cell (3, 100): inside its tube, the shifted output is at most $6/5$. -/
theorem cell_output :
    AIFSafety.Cell.Output (AIFSafety.CandidateMesh.mesh.slab 3 100) := by
  exact AIFSafety.Cells.Bin3.Slab100.shifted_output_in_mesh

/-!
## The theorem, and where it is checked {fold}

The statement below is the library's result, written out as a definition. A
definition claims nothing, and this notebook does not check it. The library's
module `AIFSafety.NotebookStatements` imports this notebook and proves these
two definitions themselves from its theorems.

The library `AIFSafety` in this repository proves it as
`AIFSafety.CompleteSafety.forward_safety`, with the time-100 form as
`hundred_safety`, from 2960 cells like the one above. The cells are composed
along each $\eta$ bin by `AIFMeshComposition.mesh_invariant`, the lemma behind
the rule above, and the eight bins cover $[8, 12]$.
At $t = 30$, eight terminal certificates put the tube inside a region where a
quadratic Lyapunov function decreases, and that function keeps the state in the
region, carrying the bound, now $x_2 \le 5/2$, to all later time.

The library is not a default build target; `lake build AIFSafety` checks all of
it. With six modules at a time on a twelve-thread machine, that takes about
five hours: 36 to 61 seconds (about 37 on average) and over 7 GB of memory per
cell, about 30 hours of processor time in all. That full build was done at
Forseti Lean v0.5.1, Asgard Lean v0.4.1 and Lean 4.35.0. Its compiled modules,
with the Forseti and Asgard modules they import, were then replayed one by one
through Lean's kernel checker `leanchecker`, and every one passed; Mathlib,
Batteries and Lean's core library were loaded from their compiled files and not
replayed. Every theorem uses only Lean's standard axioms: `propext`,
`Classical.choice` and `Quot.sound`.
-/

/-- Safety for all time: for every fixed $\eta \in [8, 12]$ the circuit has a
behaviour, and every behaviour keeps $0 \le x_2 \le 16/5$ for all $t \ge 0$. -/
def ForwardSafety : Prop :=
  ∀ eta ∈ Set.Icc (8 : ℝ) 12,
    (∃ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    ∀ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Ici (0 : ℝ),
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5

/-- After the transient: from $t = 30$ on, $x_2 \le 5/2$. -/
def LaterOutput : Prop :=
  ∀ eta ∈ Set.Icc (8 : ℝ) 12, ∀ state : Dynamics.Signal 4,
    Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t, 30 ≤ t → Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 5/2

end Notebook.AntitheticFeedback
