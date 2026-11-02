import Mathlib
import Gimle.Forseti.Syntax.Certificate
import Gimle.Forseti.Examples.GalerkinNS.K5
import Gimle.Forseti.Examples.GalerkinNS.K5Below6

/-!
# A 5-mode truncation of Navier–Stokes: the energy stays in its ball, then below its laminar level

Two-dimensional incompressible flow on the periodic square, kept to five
cosine modes of the vorticity: the three of T3 (`NS_T3.lean`) and their mirror
images under swapping the axes, so three triads, two of them mirror images
sharing only the forced mode. In simulation the energy settles at a constant
while the state circles a periodic orbit. The energy bound is proved as for
T3; this page keeps the exposition short and links there for the derivation.
The family theorem that covers every member is restated below.

Read the argument in four stages: the reusable energy bound, enstrophy
and amplitude control, the tighter quartic tube, and the decided requests.
Expand a stage for its explanation and individual claims.

**Proved.** From the start where every amplitude is $1$, a solution exists for
all $t \ge 0$, is unique, and its energy $E = \sum_k a_k^2/\lambda_k$ satisfies
$0 \le E \le 13$ throughout, and in fact $E \le 6$: below the laminar level
$\tfrac{25}{2}$, which no ball about the origin can pass, from a degree-four
tube around what is, in simulation, the flow's attractor, trapped under a
decrease that holds on the set only (`below6_contract`, the section before the claims). Decided by the
trajectory decider from named Lean contracts; the artifacts replay without the
solver. Its enstrophy $Z = \sum_k a_k^2$ satisfies
$0 \le Z \le 26$ throughout, by the same decider from a second named
contract, so every amplitude satisfies $|a_k| \le 6$ (`amplitude_bound`).

**Refuted.** $E \le 1$ for all $t \ge 0$: false at the start, where
$E = \tfrac{29}{10}$.

**Unknown.** $E \le 5$ and $Z \le 20$ for all $t \ge 0$.
The retained requests have neither a proof nor a refutation. Numerical runs
do not settle these bounds.

**Not claimed.** Anything about the Navier–Stokes *equations*: this is a
finite truncation, and nothing here says how it relates to the fluid, to other
truncations, or to the limit. Nothing about the shape of the flow beyond the
ball and the tube; the simulation is evidence, and no status reads it.

## The equations

Two-dimensional incompressible flow on the periodic square, in vorticity form,
keeps only the cosine modes $(1, 0)$, $(0, 1)$, $(1, 1)$, $(2, 1)$, $(1, 2)$ of the vorticity, with viscosity
$\nu = \tfrac{1}{10}$ and a constant force $f = 1$ on the mode $(1, 1)$.
Writing $a_k$ for the amplitude of $\cos(k \cdot x)$ and $\lambda_k = |k|^2$,
projecting the equations onto the modes gives, for every mode $k$ (the
projection is taken as read here; Lean checks everything from the
coefficients on),

$$ a_k' = -\nu \lambda_k a_k + f\,[k = (1,1)] + \sum_{\text{triads} \ni k} C_k\, a_P a_Q, $$

where $[k = (1,1)]$ is $1$ on the forced mode and $0$ otherwise, and a *triad*
$\{k, P, Q\}$ is three modes whose wavevectors, each taken with a sign, sum to
zero: $\pm k \pm P \pm Q = 0$. Its three coefficients are exact rationals fixed
by the geometry. This member has 3 triads.
In full, writing $a_{10}$ for $a_{(1,0)}$:

$$ \begin{aligned} a_{10}' &= - \tfrac{1}{10} a_{10} - \tfrac{3}{20} a_{11} a_{21} - \tfrac{1}{4} a_{01} a_{11} \\ a_{01}' &= - \tfrac{1}{10} a_{01} + \tfrac{3}{20} a_{11} a_{12} + \tfrac{1}{4} a_{10} a_{11} \\ a_{11}' &= 1 - \tfrac{1}{5} a_{11} - \tfrac{2}{5} a_{01} a_{12} + \tfrac{2}{5} a_{10} a_{21} \\ a_{21}' &= - \tfrac{1}{2} a_{21} - \tfrac{1}{4} a_{10} a_{11} \\ a_{12}' &= - \tfrac{1}{2} a_{12} + \tfrac{1}{4} a_{01} a_{11} \end{aligned} $$

## The system, compiled

The equations are declared once, in Asgard's language, and compiled to a
circuit whose exact field Lean draws and reads:
-/
namespace Notebook.NSK5
open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti Gimle.Forseti.Trajectory
  Gimle.Forseti.GalerkinNS Gimle.Forseti.Examples.GalerkinNS.K5

-- @view model Gimle.Forseti.Examples.GalerkinNS.K5.compiled
-- @evidence simulate Gimle.Forseti.Examples.GalerkinNS.K5.compiled (h := 1/100) (steps := 20000) (solver := rk4) (plane := a10, a21)

/-!
## What a simulation shows

The panel above integrates the compiled field with RK4 from the same start,
$h = \tfrac{1}{100}$ over $t \le 200$, and draws the five amplitudes and
$a_{(1,0)}$ against $a_{(2,1)}$. The energy, computed from that run, goes from
$\tfrac{29}{10}$ to a peak near $4.9$ at $t \approx 7.7$ and then settles at
$4.75$ while the state keeps circling: a periodic orbit of constant energy. That is evidence about one run and nothing more: it does not
enter any status.

## Derive the reusable energy bound {fold}

Triad cancellation gives an energy identity and a sum-of-squares certificate.
Each energy ball with threshold above $25/2$ is invariant; a start
inside it has a unique global trajectory under the family hypotheses.

### Cancel the triad energy transfers {fold}

The weights $1/\lambda_k$ cancel the cubic transfers within each triad.
The resulting identity is checked against this member's compiled field.

As in T3 (`NS_T3.lean`): each mode is a *storage element* and each triad a
*lossless three-port*, so summing the storage identities with the weights
$1/\lambda_k$ cancels every cubic term triad by triad. Here is one of this
member's triads, checked as plain arithmetic; its third coefficient vanishes
because $(1,0)$ and $(0,1)$ have the same wavenumber, so this pair feeds the
forced mode nothing:
-/

/-- The triad $\{a_{(0,1)}, a_{(1,0)}, a_{(1,1)}\}$ with weights $1/\lambda$: its three energy flows cancel exactly, and so do its
three enstrophy flows, with weights $1$. -/
theorem triad_lossless :
    (1 : ℝ) * (1/4) + (1 : ℝ) * (-1/4) + (1/2 : ℝ) * (0) = 0 ∧
    (1/4 : ℝ) + (-1/4) + (0) = 0 := by
  constructor <;> norm_num

/-!
What remains after the cancellation is the **energy identity**

$$ E' = -2\nu Z + f\, a_{(1,1)}, \qquad Z = \sum_k a_k^2, $$

which Lean checks for the compiled field by expanding both sides.
-/

/-- The energy identity for the compiled field. -/
theorem energy_rate (x : Point 5) :
    (∑ i, 2 * (![(1 / 1 : ℝ), (1 / 1 : ℝ), (1 / 2 : ℝ), (1 / 5 : ℝ), (1 / 5 : ℝ)] : Fin 5 → ℝ) i * x i * Gimle.Forseti.Nonlinear.field compiled x i) =
      -2 * (1 / 10 : ℝ) * (x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 + x 4 * x 4) + (1 / 1 : ℝ) * x 2 := by
  rw [field_eq]
  exact energy_identity x

/-!
### Turn the identity into a trapping ball {fold}

Energy decreases above $25/2$. The ball $E \le 13$ therefore
traps any trajectory starting inside it, including the all-ones start.

As in T3 (`NS_T3.lean`), $Z \ge E$ and the forcing acts on one mode, so the
energy identity gives $2\nu(f^2/(8\nu^2) - E) - E' \ge 0$ with an explicit
sum-of-squares certificate, checked below for this member's field. So $E$
decreases whenever it exceeds $f^2/(8\nu^2) = \tfrac{25}{2}$, and any ball
above that level traps the flow forever. The level is not an artefact of the
proof: the laminar state, with only the forced mode excited at
$a_{(1,1)} = f/(2\nu)$, is an equilibrium with exactly that energy, and the
trajectory from rest along the forced mode alone,
$a_{(1,1)}(t) = \tfrac{f}{2\nu}(1 - e^{-2\nu t})$ with every other mode at zero
(a single mode feeds no triad), climbs from $E = 0$ to it, so every smaller
ball is left.
The claim below uses $13$, a whisker above.
-/

/-- The laminar equilibrium's energy, the least trappable level. -/
theorem laminar_energy : (1 : ℝ) ^ 2 / (8 * (1/10) ^ 2) = 25/2 := by
  norm_num

/-- The certificate, checked for the compiled field: the gap is a sum of squares. -/
theorem certificate_here (x : Point 5) :
    trapping.alpha * (trapping.inner - trapping.energy x) - trapping.rate (Gimle.Forseti.Nonlinear.field compiled) x =
      (1 / 10 : ℝ) * (x 2 - 5 / 1) ^ 2 + (4 / 25 : ℝ) * x 3 ^ 2 + (4 / 25 : ℝ) * x 4 ^ 2 := by
  exact certificate x

/-!
### Connect this system to the finite family {fold}

The compiled field is an instance of the family field. The theorem applies
to nonzero modes with forcing on $(1,1)$ and an initial state inside
$E \le C$, where $C>25/2$.

The family theorem (`GalerkinNS.Family`; derivation and discussion in
`NS_T3.lean`) is instantiated here: Lean restates the library's check that
this member's compiled field is the family field at its modes, and the
theorem at $\nu = \tfrac{1}{10}$, $f = 1$ — existence for all $t \ge$ any start
time, uniqueness and $E \le C$ for every list of nonzero modes forced on
$(1,1)$ and every $C > f^2/(8\nu^2)$, provided the initial energy is at most $C$.
-/

/-- This member's compiled field is the family field at its modes (the library's
`field_eq_family`, restated). -/
theorem is_family_member :
    Nonlinear.field compiled = Family.field (1 / 10 : ℝ) (1 / 1 : ℝ) modes forcedIndex := by
  exact field_eq_family

/-- **Every member.** At $\nu = \tfrac{1}{10}$, $f = 1$: for any nonzero modes
containing $(1,1)$ and any $C > \tfrac{25}{2}$, from a start with $E \le C$ a
solution exists for all $t \ge$ any start time, is unique, and keeps
$E \le C$; the forcing sits on the mode $(1,1)$. -/
theorem every_member {n : ℕ} (k : Fin n → Family.Wave) (hk : ∀ i, k i ≠ 0) (forced : Fin n)
    (hf : k forced = (1, 1)) (C : ℝ) (hC : (1 : ℝ) ^ 2 / (8 * (1 / 10 : ℝ) ^ 2) < C)
    (time : TimeDomain) (x₀ : Point n) (initial : Family.energy k x₀ ≤ C) :
    (∃ state, Nonlinear.Solves (Family.field (1 / 10 : ℝ) 1 k forced) time x₀ state) ∧
    (∀ x y : Signal n, Nonlinear.Solves (Family.field (1 / 10 : ℝ) 1 k forced) time x₀ x →
      Nonlinear.Solves (Family.field (1 / 10 : ℝ) 1 k forced) time x₀ y →
        Set.EqOn x y time.domain) ∧
    (∀ state, Nonlinear.Solves (Family.field (1 / 10 : ℝ) 1 k forced) time x₀ state →
      ∀ t ∈ time.domain, Family.energy k (state t) ≤ C) := by
  exact Family.trapped (1 / 10 : ℝ) 1 (by norm_num) k hk forced hf C hC time x₀ initial

/-!
## Bound enstrophy and individual amplitudes {fold}

The enstrophy certificate gives $Z \le 26$ for the stated start, hence
$|a_k| \le 6$ for every amplitude. Energy and enstrophy span the diagonal
quadratic forms conserved by the nonlinear triad transfers; forcing and
damping still change them along the full flow.

### Derive the enstrophy certificate {fold}

The triads conserve enstrophy as well as energy. Its dissipation identity
supplies a second trapping certificate and a bound on each amplitude.

The triads are lossless for the weights $1$ as well as for $1/\lambda_k$
(`triad_lossless` above states both for one triad; the member file does for
every triad), so the enstrophy
$Z = \sum_k a_k^2$ has an identity of its own,
$Z' = -2\nu \sum_k \lambda_k a_k^2 + 2 f a_{(1,1)}$, and a certificate of its own,
$2\nu(f^2/(4\nu^2) - Z) - Z' = 2\nu \sum_{k \ne (1,1)} (\lambda_k - 1) a_k^2 + 2\nu (a_{(1,1)} - f/(2\nu))^2$.
The level $f^2/(4\nu^2) = 25$ is again the laminar state's, and every ball
above it traps, for every member of the family (forseti-lean's
`Family.trapped_enstrophy`; the level does not depend on the modes). What the
enstrophy ball adds: it bounds every amplitude by $\sqrt{C}$, where the energy
ball bounds $a_k$ only by $\sqrt{\lambda_k C}$; here every amplitude stays
within $\sqrt{26} < 6$ for all time, as `amplitude_bound`
says of any state in the ball the decider establishes below.

-/

/-- The enstrophy identity for the compiled field. -/
theorem enstrophy_rate (x : Point 5) :
    (∑ i, 2 * x i * Gimle.Forseti.Nonlinear.field Gimle.Forseti.Examples.GalerkinNS.K5.compiled x i) =
      -2 * (1 / 10 : ℝ) * (x 0 * x 0 + x 1 * x 1 + (2 / 1 : ℝ) * x 2 * x 2 + (5 / 1 : ℝ) * x 3 * x 3 + (5 / 1 : ℝ) * x 4 * x 4) + 2 * (1 / 1 : ℝ) * x 2 := by
  rw [Gimle.Forseti.Examples.GalerkinNS.K5.field_eq]
  exact Gimle.Forseti.Examples.GalerkinNS.K5.enstrophy_identity x

/-- The laminar state's enstrophy, the least trappable level. -/
theorem laminar_enstrophy : (1 / 1 : ℝ) ^ 2 / (4 * (1 / 10) ^ 2) = 25 / 1 := by
  norm_num

/-- The enstrophy certificate, checked for the compiled field: the gap is a sum of squares. -/
theorem enstrophy_certificate_here (x : Point 5) :
    Gimle.Forseti.Examples.GalerkinNS.K5.trappingZ.alpha * (Gimle.Forseti.Examples.GalerkinNS.K5.trappingZ.inner - Gimle.Forseti.Examples.GalerkinNS.K5.trappingZ.energy x) - Gimle.Forseti.Examples.GalerkinNS.K5.trappingZ.rate (Gimle.Forseti.Nonlinear.field Gimle.Forseti.Examples.GalerkinNS.K5.compiled) x =
      (2 * (1 / 10) : ℝ) * (x 2 - 5 / 1) ^ 2 + (4 / 5 : ℝ) * x 3 ^ 2 + (4 / 5 : ℝ) * x 4 ^ 2 := by
  exact Gimle.Forseti.Examples.GalerkinNS.K5.certificateZ x

/-- In the enstrophy ball every amplitude is bounded: $a_k^2 \le Z \le 26$. -/
theorem amplitude_bound (x : Point 5) (h : Gimle.Forseti.Examples.GalerkinNS.K5.enstrophy x ≤ 26) (i : Fin 5) :
    |x i| ≤ 6 := by
  rw [Gimle.Forseti.Examples.GalerkinNS.K5.enstrophy_eq_trappingZ, Gimle.Forseti.Examples.GalerkinNS.K5.enstrophy_eq_family] at h
  have := Gimle.Forseti.GalerkinNS.Family.mode_sq_le_enstrophy x i
  rw [abs_le]
  constructor <;> nlinarith


/-!
### Classify the diagonal transfer invariants {fold}

Every diagonal weighting for which the triads are lossless is a combination
of $1/\lambda$ and $1$. This classifies diagonal quadratic forms for the
nonlinear transfers, not all invariants of the full forced, damped system.

The two trapping balls can be intersected to give
$\{E \le C_E\} \cap \{Z \le C_Z\}$. A closed trapping set containing the
origin also contains the laminar equilibrium approached from that origin,
so it cannot establish the requested energy bound $5$.
-/

/-- **Only two diagonal invariants.** Every weighting for which this member's
triads are lossless is a combination of $1/\lambda$ and $1$. -/
theorem only_two (w : Fin 5 → ℝ)
    (h0 : w 0 * (-1 / 4) + w 1 * (1 / 4) = 0)
    (h1 : w 1 * (3 / 20) + w 2 * (-2 / 5) + w 4 * (1 / 4) = 0)
    (h2 : w 0 * (-3 / 20) + w 2 * (2 / 5) + w 3 * (-1 / 4) = 0) :
    ∃ α β : ℝ, w 0 = α * (1 / 1) + β ∧
      w 1 = α * (1 / 1) + β ∧
      w 2 = α * (1 / 2) + β ∧
      w 3 = α * (1 / 5) + β ∧
      w 4 = α * (1 / 5) + β := by
  exact Gimle.Forseti.Examples.GalerkinNS.K5.only_two_diagonal w h0 h1 h2


/-!
### Inspect the extra non-diagonal identity {fold}

K5 has a quadratic form with cross terms whose flux has no cubic part.
The checked identity still has a quadratic right-hand side: it does not
say this form is constant along the full forced, damped flow. It does not
contradict the classification of diagonal transfer invariants.
-/

/-- A third conserved quadratic form, from this member's reflection symmetry
$(1,0) \leftrightarrow (0,1)$, $(2,1) \leftrightarrow (1,2)$: its flux along the
field has no cubic part. It is not diagonal, so it is no counterexample to
`only_two`. That T3 and B2 have no third symmetric form is an exact nullspace
computation in the design study, not a theorem checked here. -/
theorem symmetric_invariant (x : Point 5) :
    ((2 / 1 : ℝ) * x 4 + (10 / 3 : ℝ) * x 0) * field x 0 + ((2 / 1 : ℝ) * x 3 + (10 / 3 : ℝ) * x 1) * field x 1 + ((2 / 1 : ℝ) * x 1) * field x 3 + ((2 / 1 : ℝ) * x 0) * field x 4 = (-6 / 5 : ℝ) * x 1 * x 3 + (-1 / 3 : ℝ) * x 1 * x 1 + (-6 / 5 : ℝ) * x 0 * x 4 + (-1 / 3 : ℝ) * x 0 * x 0 := by
  exact Gimle.Forseti.Examples.GalerkinNS.K5.symmetric_invariant_0 x


/-!
## Sharpen the bound with a quartic tube {fold}

A degree-four tube contains the all-ones start, excludes the laminar
equilibrium, and gives $E \le 6$. Its decrease certificate holds on the
trapping set. The stronger request $E \le 5$ remains unknown.

Every set the global decrease can trap contains every equilibrium: at an
equilibrium the rate is zero, so $V' \le \alpha(C' - V)$ forces $V \le C'$ there.
The laminar state $(0, 0, 5, 0, 0)$ is an equilibrium (`laminar_equilibrium`),
so no such set, whatever its weights or centre, has $\max E$ below
$\tfrac{25}{2}$. A set that excludes it needs a decrease that holds *on the set
only*, which the library takes for a general polynomial $V$ (`PolynomialTrapping`,
by a barrier lemma).

Where this flow goes is not a point. In simulation (evidence, never a status)
the start settles on a **rotating wave**: the forced amplitude sits at
$a_{11} \approx 1.317$ while $a_{10} + i\,a_{01}$ and $a_{21} + i\,a_{12}$
keep constant moduli ($1.907$ and $1.101$) and rotate at equal and opposite
rates, period about $22.9$, with $E \approx 4.748$ constant — a relative
equilibrium of the field's rotation symmetry. The search found no ellipsoid
that traps it; it found (the design study's spike, task 213) a thin
**degree-four tube**
$V \le 1$ around it that holds the start, excludes the laminar point
($V \approx 500$ there) and lies inside $E \le 6$, on which the decrease holds
by an explicit degree-six sum of squares with a multiplier $\sigma \ge 0$. All
of it is rational and every identity is `ring`; the library states the
contract `below6_contract`, and the decider cites it below.
-/

/-- The laminar state is an equilibrium of the compiled field, restated. -/
theorem laminar_is_equilibrium : field ![0, 0, 5, 0, 0] = 0 := by
  exact laminar_equilibrium

/-- The tube excludes it and holds the start, restated. -/
theorem tube_excludes_laminar : 1 < Gimle.Forseti.Examples.GalerkinNS.K5.V ![0, 0, 5, 0, 0] ∧
    Gimle.Forseti.Examples.GalerkinNS.K5.V ![1, 1, 1, 1, 1] < 1 := by
  exact ⟨laminar_outside, start_inside⟩

/-- Inside the tube the energy is at most `6`, restated. -/
theorem tube_below_six (x : Point 5) (hx : Gimle.Forseti.Examples.GalerkinNS.K5.V x ≤ 1) :
    energy x ≤ 6 := by
  exact contained x hx

/-!
## Inspect the decided trajectory contracts {fold}

The queries certify energy bound $13$ and the sharper bound $6$,
and enstrophy bound $26$, from the all-ones start at time zero. Energy
bound $1$ is refuted; $E \le 5$ and $Z \le 20$ remain unknown.
Unknown requests may have no claim card, so claim counts do not list every
unresolved query.

Existence for all time, uniqueness and the sets come from the library's
trapping theorems: the ball from the general one that traps the Lorenz system
(`Lorenz.lean`), the tube from its polynomial variant with the decrease on the
set, both by clamping the field to a box, solving on every $[0, n]$, gluing,
and fencing at the boundary. Every claim below is decided against the compiled
circuit.
-/


/-!
### Inspect the energy bound of 13 {fold}

The query certifies existence, uniqueness and $0 \le E \le 13$ for
all time from the all-ones start.
-/

-- @decide in_ball : trajectory ns-k5 from (1, 1, 1, 1, 1) at 0 observe E always : E >= 0 and E <= 13

namespace DecidedShared_c7e9c8d9daff

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 5 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 8 := ⟨5, by decide⟩

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.GalerkinNS.K5.evolution.states.map (·.initialId) = ["initial-a10", "initial-a01", "initial-a11", "initial-a21", "initial-a12"] ∧
  (Gimle.Forseti.Examples.GalerkinNS.K5.body.observations.get forsetiObservation).port.id =
    "obs-e" ∧
  Gimle.Forseti.Examples.GalerkinNS.K5.evolution.axis.id = "time"

end DecidedShared_c7e9c8d9daff

namespace Decided_in_ball

open DecidedShared_c7e9c8d9daff

example : @forsetiTime = @DecidedShared_c7e9c8d9daff.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_c7e9c8d9daff.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_c7e9c8d9daff.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_c7e9c8d9daff.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (13) 1))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["E"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (6) 1)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.K5.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- E is output 5 of the compiled circuit, the port obs-e; the input's initial wires (initial-a10, initial-a01, initial-a11, initial-a21, initial-a12) start at (1, 1, 1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-k5 interpretation continuous-real obligation contract start time = 0 initial initial-a01 = 1, initial-a10 = 1, initial-a11 = 1, initial-a12 = 1, initial-a21 = 1 observe obs-e as E always : E >= 0 and E <= 13 -/
theorem in_ball :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.K5.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 5),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 5; E ≥ 0 ∧ E ≤ 13) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.K5.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.K5.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.K5.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.K5.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.K5.energyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.K5.below6_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[((mkRat (7) 1), (.constant (mkRat (1) 1)))]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (13) 1) : ℚ) : ℝ) = 13 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiContract) => bridge.mpr (show forsetiIdentities ∧ forsetiContract from root).2) ?_
  constructor
  · intro claim
    unfold forsetiContract
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at claim
    refine ⟨?_, ?_, ?_⟩ <;> set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc]
    · exact fun u start => (claim u start).1
    · exact fun u start => (claim u start).2.1
    · exact fun u start => (claim u start).2.2
  · intro lane
    unfold forsetiContract at lane
    obtain ⟨realizable, unique, holds⟩ := lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at realizable unique holds ⊢
    exact fun u start => ⟨realizable u start, unique u start, holds u start⟩


/-!
### Inspect the refuted energy bound of one {fold}

The initial energy is $29/10>1$. A checked refutation is retained
beside the notebook; the false positive claim deliberately uses `sorry`.
-/

end Decided_in_ball


-- @decide below_one : trajectory ns-k5 from (1, 1, 1, 1, 1) at 0 observe E always : E <= 1

namespace Decided_below_one

open DecidedShared_c7e9c8d9daff

example : @forsetiTime = @DecidedShared_c7e9c8d9daff.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_c7e9c8d9daff.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_c7e9c8d9daff.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_c7e9c8d9daff.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1)))))

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.K5.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- E is output 5 of the compiled circuit, the port obs-e; the input's initial wires (initial-a10, initial-a01, initial-a11, initial-a21, initial-a12) start at (1, 1, 1, 1, 1) at time = 0. The trajectory decider refuted it. Goal (trajectory): trajectory ns-k5 interpretation continuous-real obligation contract start time = 0 initial initial-a01 = 1, initial-a10 = 1, initial-a11 = 1, initial-a12 = 1, initial-a21 = 1 observe obs-e as E always : E <= 1 -/
theorem below_one :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.K5.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 5),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 5; E ≤ 1) := by
  sorry

theorem below_one_refuted : ¬ (have circuit := Gimle.Forseti.Examples.GalerkinNS.K5.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 5),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 5; E ≤ 1)) := by
  have refuted : forsetiIdentities ∧ ¬ forsetiContract := by
    unfold forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    intro contract
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.K5.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.K5.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.K5.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.K5.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.K5.energyIndex := rfl
    rw [time, init, obs] at contract
    obtain ⟨state, realized⟩ := Gimle.Forseti.Examples.GalerkinNS.K5.compiled_exists
    have start : state Gimle.Forseti.Examples.GalerkinNS.K5.evolution.time.start = Gimle.Forseti.Examples.GalerkinNS.K5.compiled.initial := by unfold Gimle.Asgard.Model.ContinuousModel.Realizes Gimle.Asgard.Model.ContinuousModel.feedback at realized; exact ((Gimle.Forseti.Trajectory.close_rel _ _ _ _ _ _).mp realized).2.1
    have bounded := contract.holds _ Gimle.Forseti.Examples.GalerkinNS.K5.declared_input_admitted _ ⟨state, (Gimle.Forseti.Examples.GalerkinNS.K5.feedback_reads _ Gimle.Forseti.Examples.GalerkinNS.K5.declared_input_admitted state).mpr realized, rfl⟩ Gimle.Forseti.Examples.GalerkinNS.K5.evolution.time.start (by simp [Gimle.Asgard.Dynamics.TimeDomain.domain])
    simp only at bounded
    rw [start, Gimle.Forseti.Examples.GalerkinNS.K5.energy_at_initial] at bounded
    have witness : forsetiPost.holds (fun i => (((fun _ : Fin 1 => (mkRat (29) 10)) i : ℚ) : ℝ)) := by convert bounded using 2; norm_num [Rat.mkRat_eq_div]
    rw [← Gimle.Forseti.Syntax.Formula.holdsQ_iff] at witness
    exact absurd witness (by decide +kernel)
  intro claim
  have forsetiCast0 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiContract) => refuted.2 (bridge.mp claim)) ?_
  constructor
  · intro claim
    unfold forsetiContract
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at claim
    refine ⟨?_, ?_, ?_⟩ <;> set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc]
    · exact fun u start => (claim u start).1
    · exact fun u start => (claim u start).2.1
    · exact fun u start => (claim u start).2.2
  · intro lane
    unfold forsetiContract at lane
    obtain ⟨realizable, unique, holds⟩ := lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at realizable unique holds ⊢
    exact fun u start => ⟨realizable u start, unique u start, holds u start⟩


/-!
### Inspect the sharper energy bound of six {fold}

The quartic-tube contract certifies $E \le 6$ for this initialized
trajectory. The later request $E \le 5$ remains unresolved.
-/

end Decided_below_one


-- @decide below_6 : trajectory ns-k5 from (1, 1, 1, 1, 1) at 0 observe E always : E <= 6

namespace Decided_below_6

open DecidedShared_c7e9c8d9daff

example : @forsetiTime = @DecidedShared_c7e9c8d9daff.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_c7e9c8d9daff.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_c7e9c8d9daff.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_c7e9c8d9daff.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (6) 1)))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["E"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (6) 1)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.K5.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- E is output 5 of the compiled circuit, the port obs-e; the input's initial wires (initial-a10, initial-a01, initial-a11, initial-a21, initial-a12) start at (1, 1, 1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-k5 interpretation continuous-real obligation contract start time = 0 initial initial-a01 = 1, initial-a10 = 1, initial-a11 = 1, initial-a12 = 1, initial-a21 = 1 observe obs-e as E always : E <= 6 -/
theorem below_6 :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.K5.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 5),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 5; E ≤ 6) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.K5.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.K5.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.K5.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.K5.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.K5.energyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.K5.below6_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (6) 1) : ℚ) : ℝ) = 6 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiContract) => bridge.mpr (show forsetiIdentities ∧ forsetiContract from root).2) ?_
  constructor
  · intro claim
    unfold forsetiContract
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at claim
    refine ⟨?_, ?_, ?_⟩ <;> set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc]
    · exact fun u start => (claim u start).1
    · exact fun u start => (claim u start).2.1
    · exact fun u start => (claim u start).2.2
  · intro lane
    unfold forsetiContract at lane
    obtain ⟨realizable, unique, holds⟩ := lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at realizable unique holds ⊢
    exact fun u start => ⟨realizable u start, unique u start, holds u start⟩


/-!
### Compare unresolved energy with certified enstrophy {fold}

The request $E \le 5$ remains unknown. The next request certifies
existence, uniqueness and $0 \le Z \le 26$ from the stated start,
supporting the amplitude bound above. The later request $Z \le 20$
also remains unknown.
-/

end Decided_below_6


-- @decide below_5 : trajectory ns-k5 from (1, 1, 1, 1, 1) at 0 observe E always : E <= 5

-- @decide in_enstrophy_ball : trajectory ns-k5 from (1, 1, 1, 1, 1) at 0 observe Z always : Z >= 0 and Z <= 26

namespace DecidedShared_41629943fbbd

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 5 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 8 := ⟨6, by decide⟩

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.GalerkinNS.K5.evolution.states.map (·.initialId) = ["initial-a10", "initial-a01", "initial-a11", "initial-a21", "initial-a12"] ∧
  (Gimle.Forseti.Examples.GalerkinNS.K5.body.observations.get forsetiObservation).port.id =
    "obs-z" ∧
  Gimle.Forseti.Examples.GalerkinNS.K5.evolution.axis.id = "time"

end DecidedShared_41629943fbbd

namespace Decided_in_enstrophy_ball

open DecidedShared_41629943fbbd

example : @forsetiTime = @DecidedShared_41629943fbbd.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_41629943fbbd.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_41629943fbbd.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_41629943fbbd.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (26) 1))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["Z"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (26) 1)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.K5.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- Z is output 6 of the compiled circuit, the port obs-z; the input's initial wires (initial-a10, initial-a01, initial-a11, initial-a21, initial-a12) start at (1, 1, 1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-k5 interpretation continuous-real obligation contract start time = 0 initial initial-a01 = 1, initial-a10 = 1, initial-a11 = 1, initial-a12 = 1, initial-a21 = 1 observe obs-z as Z always : Z >= 0 and Z <= 26 -/
theorem in_enstrophy_ball :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.K5.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 5),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 8, circuit.Rel time u y →
        ∀ t ≥ 0, have Z := y t 6; Z ≥ 0 ∧ Z ≤ 26) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.K5.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.K5.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.K5.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.K5.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.K5.enstrophyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.K5.enstrophy_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (26) 1) : ℚ) : ℝ) = 26 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiContract) => bridge.mpr (show forsetiIdentities ∧ forsetiContract from root).2) ?_
  constructor
  · intro claim
    unfold forsetiContract
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at claim
    refine ⟨?_, ?_, ?_⟩ <;> set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc]
    · exact fun u start => (claim u start).1
    · exact fun u start => (claim u start).2.1
    · exact fun u start => (claim u start).2.2
  · intro lane
    unfold forsetiContract at lane
    obtain ⟨realizable, unique, holds⟩ := lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at realizable unique holds ⊢
    exact fun u start => ⟨realizable u start, unique u start, holds u start⟩


/-!
## Scope and unresolved bounds

These are statements about the compiled finite ODE at the stated viscosity,
forcing and initial state. They establish no approximation or limiting
theorem for the Navier–Stokes PDE. Simulations guide the questions but are
not proofs. The requests $E \le 5$ and $Z \le 20$ remain unknown;
their absence from claim counts does not make them settled.
-/

end Decided_in_enstrophy_ball


-- @decide enstrophy_below_20 : trajectory ns-k5 from (1, 1, 1, 1, 1) at 0 observe Z always : Z <= 20

#print axioms triad_lossless
#print axioms energy_rate
#print axioms laminar_energy
#print axioms laminar_is_equilibrium
#print axioms tube_excludes_laminar
#print axioms tube_below_six
#print axioms certificate_here
#print axioms is_family_member
#print axioms every_member
#print axioms enstrophy_rate
#print axioms laminar_enstrophy
#print axioms enstrophy_certificate_here
#print axioms amplitude_bound
#print axioms only_two
#print axioms symmetric_invariant

end Notebook.NSK5
