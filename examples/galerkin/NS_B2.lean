import Mathlib
import Gimle.Forseti.Syntax.Certificate
import Gimle.Forseti.Examples.GalerkinNS.B2

/-!
# A 12-mode truncation of Navier–Stokes: the energy stays in its ball

Two-dimensional incompressible flow on the periodic square, kept to the twelve
cosine modes of the vorticity with wavevectors in the block
$|k_x|, |k_y| \le 2$, forced in $(1, 1)$ and damped in all, at a viscosity
($\nu = \tfrac{1}{50}$)
where the simulated flow wanders irregularly for as long as it is run, and is
still trapped. The energy bound is proved as for T3 (`NS_T3.lean`), from
twenty-two triads instead of one; this page keeps the exposition short and
links there for the derivation. The family theorem that covers every member
is restated below.

Read the argument in three stages: the reusable energy bound, enstrophy
and amplitude control, and the decided requests. Expand a stage for its
explanation and individual claims.

**Proved.** From the start where every amplitude is $1$, a solution exists for
all $t \ge 0$, is unique, and its energy $E = \sum_k a_k^2/\lambda_k$ satisfies
$0 \le E \le 313$ throughout. Decided by the trajectory decider from a
named Lean contract; its artifact replays without the solver. Its enstrophy $Z = \sum_k a_k^2$ satisfies
$0 \le Z \le 626$ throughout, by the same decider from a second named
contract, so every amplitude satisfies $|a_k| \le 26$ (`amplitude_bound`).

**Refuted.** $E \le 1$ for all $t \ge 0$: false at the start, where
$E = \tfrac{91}{20}$.

**Unknown.** $E \le 150$ and $Z \le 600$ for all $t \ge 0$.
The retained requests have neither a proof nor a refutation. Numerical runs
do not settle these bounds.

**Not claimed.** Anything about the Navier–Stokes *equations*: this is a
finite truncation, and nothing here says how it relates to the fluid, to other
truncations, or to the limit. Nothing about the shape of the flow beyond the
ball; the simulation is evidence, and no status reads it.

## The equations

Two-dimensional incompressible flow on the periodic square, in vorticity form,
keeps only the cosine modes $(0, 1)$, $(0, 2)$, $(1, -2)$, $(1, -1)$, $(1, 0)$, $(1, 1)$, $(1, 2)$, $(2, -2)$, $(2, -1)$, $(2, 0)$, $(2, 1)$, $(2, 2)$ of the vorticity, with viscosity
$\nu = \tfrac{1}{50}$ and a constant force $f = 1$ on the mode $(1, 1)$.
Writing $a_k$ for the amplitude of $\cos(k \cdot x)$ and $\lambda_k = |k|^2$,
projecting the equations onto the modes gives, for every mode $k$ (the
projection is taken as read here; Lean checks everything from the
coefficients on),

$$ a_k' = -\nu \lambda_k a_k + f\,[k = (1,1)] + \sum_{\text{triads} \ni k} C_k\, a_P a_Q, $$

where $[k = (1,1)]$ is $1$ on the forced mode and $0$ otherwise, and a *triad*
$\{k, P, Q\}$ is three modes whose wavevectors, each taken with a sign, sum to
zero: $\pm k \pm P \pm Q = 0$. Its three coefficients are exact rationals fixed
by the geometry. This member has 22 triads.
Twelve equations with up to a dozen terms each; Lean draws them below rather
than this page listing them.

## The system, compiled

The equations are declared once, in Asgard's language, and compiled to a
circuit whose exact field Lean draws and reads:
-/
namespace Notebook.NSB2
open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti Gimle.Forseti.Trajectory
  Gimle.Forseti.GalerkinNS Gimle.Forseti.Examples.GalerkinNS.B2

-- @view model Gimle.Forseti.Examples.GalerkinNS.B2.compiled
-- @evidence simulate Gimle.Forseti.Examples.GalerkinNS.B2.compiled (h := 1/50) (steps := 10000) (solver := rk4) (plane := a11, a21)

/-!
## What a simulation shows

The panel above integrates the compiled field with RK4 from the same start,
$h = \tfrac{1}{50}$ over $t \le 200$, and draws the twelve amplitudes and
$a_{(1,1)}$ against $a_{(2,1)}$. The energy, computed from that run, goes from
$\tfrac{91}{20}$ to a peak near $98$ at $t \approx 99$, falls back to about $75$
by $t \approx 140$ and stays within $74$–$77$ to the end, the amplitudes
oscillating with a period near $1.35$. Runs we made of the same equations at
other steps, outside the workbench and not kept here, tell other stories:
at $h = \tfrac{1}{100}$ the energy wandered between about $19$ and $98$ and kept
wandering to $t = 2000$, peaking near $103$; at $h = \tfrac{1}{200}$ it settled
on an orbit near $E = 71.5$. That sensitivity to the integrator is why this
page says *irregular in simulation* and no more. It is evidence about runs,
not a status.

## Derive the reusable energy bound {fold}

Triad cancellation gives an energy identity and a sum-of-squares certificate.
Each energy ball with threshold above $625/2$ is invariant; a start
inside it has a unique global trajectory under the family hypotheses.

### Cancel the triad energy transfers {fold}

The weights $1/\lambda_k$ cancel the cubic transfers within each triad.
The resulting identity is checked against this member's compiled field.

As in T3 (`NS_T3.lean`): each mode is a *storage element* and each triad a
*lossless three-port*, so summing the storage identities with the weights
$1/\lambda_k$ cancels every cubic term triad by triad. Here is one of this
member's triads, checked as plain arithmetic:
-/

/-- The triad $\{a_{(0,1)}, a_{(1,-2)}, a_{(1,-1)}\}$ with weights $1/\lambda$: its three energy flows cancel exactly, and so do its
three enstrophy flows, with weights $1$. -/
theorem triad_lossless :
    (1 : ℝ) * (-3/20) + (1/5 : ℝ) * (-1/4) + (1/2 : ℝ) * (2/5) = 0 ∧
    (-3/20 : ℝ) + (-1/4) + (2/5) = 0 := by
  constructor <;> norm_num

/-!
What remains after the cancellation is the **energy identity**

$$ E' = -2\nu Z + f\, a_{(1,1)}, \qquad Z = \sum_k a_k^2, $$

which Lean checks for the compiled field by expanding both sides.
-/

/-- The energy identity for the compiled field. -/
theorem energy_rate (x : Point 12) :
    (∑ i, 2 * (![(1 / 1 : ℝ), (1 / 4 : ℝ), (1 / 5 : ℝ), (1 / 2 : ℝ), (1 / 1 : ℝ), (1 / 2 : ℝ), (1 / 5 : ℝ), (1 / 8 : ℝ), (1 / 5 : ℝ), (1 / 4 : ℝ), (1 / 5 : ℝ), (1 / 8 : ℝ)] : Fin 12 → ℝ) i * x i * Gimle.Forseti.Nonlinear.field compiled x i) =
      -2 * (1 / 50 : ℝ) * (x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 + x 4 * x 4 + x 5 * x 5 + x 6 * x 6 + x 7 * x 7 + x 8 * x 8 + x 9 * x 9 + x 10 * x 10 + x 11 * x 11) + (1 / 1 : ℝ) * x 5 := by
  rw [field_eq]
  exact energy_identity x

/-!
### Turn the identity into a trapping ball {fold}

Energy decreases above $625/2$. The ball $E \le 313$ therefore
traps any trajectory starting inside it, including the all-ones start.

As in T3 (`NS_T3.lean`), $Z \ge E$ and the forcing acts on one mode, so the
energy identity gives $2\nu(f^2/(8\nu^2) - E) - E' \ge 0$ with an explicit
sum-of-squares certificate, checked below for this member's field. So $E$
decreases whenever it exceeds $f^2/(8\nu^2) = \tfrac{625}{2}$, and any ball
above that level traps the flow forever. The level is not an artefact of the
proof: the laminar state, with only the forced mode excited at
$a_{(1,1)} = f/(2\nu)$, is an equilibrium with exactly that energy, and the
trajectory from rest along the forced mode alone,
$a_{(1,1)}(t) = \tfrac{f}{2\nu}(1 - e^{-2\nu t})$ with every other mode at zero
(a single mode feeds no triad), climbs from $E = 0$ to it, so every smaller
ball is left.
The claim below uses $313$, a whisker above.
-/

/-- The laminar equilibrium's energy, the least trappable level. -/
theorem laminar_energy : (1 : ℝ) ^ 2 / (8 * (1/50) ^ 2) = 625/2 := by
  norm_num

/-- The certificate, checked for the compiled field: the gap is a sum of squares. -/
theorem certificate_here (x : Point 12) :
    trapping.alpha * (trapping.inner - trapping.energy x) - trapping.rate (Gimle.Forseti.Nonlinear.field compiled) x =
      (1 / 50 : ℝ) * (x 5 - 25 / 1) ^ 2 + (3 / 100 : ℝ) * x 1 ^ 2 + (4 / 125 : ℝ) * x 2 ^ 2 + (1 / 50 : ℝ) * x 3 ^ 2 + (4 / 125 : ℝ) * x 6 ^ 2 + (7 / 200 : ℝ) * x 7 ^ 2 + (4 / 125 : ℝ) * x 8 ^ 2 + (3 / 100 : ℝ) * x 9 ^ 2 + (4 / 125 : ℝ) * x 10 ^ 2 + (7 / 200 : ℝ) * x 11 ^ 2 := by
  exact certificate x

/-!
### Connect this system to the finite family {fold}

The compiled field is an instance of the family field. The theorem applies
to nonzero modes with forcing on $(1,1)$ and an initial state inside
$E \le C$, where $C>625/2$.

The family theorem (`GalerkinNS.Family`; derivation and discussion in
`NS_T3.lean`) is instantiated here: Lean restates the library's check that
this member's compiled field is the family field at its modes, and the
theorem at $\nu = \tfrac{1}{50}$, $f = 1$ — existence for all $t \ge$ any start
time, uniqueness and $E \le C$ for every list of nonzero modes forced on
$(1,1)$ and every $C > f^2/(8\nu^2)$, provided the initial energy is at most $C$.
-/

/-- This member's compiled field is the family field at its modes (the library's
`field_eq_family`, restated). -/
theorem is_family_member :
    Nonlinear.field compiled = Family.field (1 / 50 : ℝ) (1 / 1 : ℝ) modes forcedIndex := by
  exact field_eq_family

/-- **Every member.** At $\nu = \tfrac{1}{50}$, $f = 1$: for any nonzero modes
containing $(1,1)$ and any $C > \tfrac{625}{2}$, from a start with $E \le C$ a
solution exists for all $t \ge$ any start time, is unique, and keeps
$E \le C$; the forcing sits on the mode $(1,1)$. -/
theorem every_member {n : ℕ} (k : Fin n → Family.Wave) (hk : ∀ i, k i ≠ 0) (forced : Fin n)
    (hf : k forced = (1, 1)) (C : ℝ) (hC : (1 : ℝ) ^ 2 / (8 * (1 / 50 : ℝ) ^ 2) < C)
    (time : TimeDomain) (x₀ : Point n) (initial : Family.energy k x₀ ≤ C) :
    (∃ state, Nonlinear.Solves (Family.field (1 / 50 : ℝ) 1 k forced) time x₀ state) ∧
    (∀ x y : Signal n, Nonlinear.Solves (Family.field (1 / 50 : ℝ) 1 k forced) time x₀ x →
      Nonlinear.Solves (Family.field (1 / 50 : ℝ) 1 k forced) time x₀ y →
        Set.EqOn x y time.domain) ∧
    (∀ state, Nonlinear.Solves (Family.field (1 / 50 : ℝ) 1 k forced) time x₀ state →
      ∀ t ∈ time.domain, Family.energy k (state t) ≤ C) := by
  exact Family.trapped (1 / 50 : ℝ) 1 (by norm_num) k hk forced hf C hC time x₀ initial

/-!
## Bound enstrophy and individual amplitudes {fold}

The enstrophy certificate gives $Z \le 626$ for the stated start, hence
$|a_k| \le 26$ for every amplitude. Energy and enstrophy span the diagonal
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
The level $f^2/(4\nu^2) = 625$ is again the laminar state's, and every ball
above it traps, for every member of the family (forseti-lean's
`Family.trapped_enstrophy`; the level does not depend on the modes). What the
enstrophy ball adds: it bounds every amplitude by $\sqrt{C}$, where the energy
ball bounds $a_k$ only by $\sqrt{\lambda_k C}$; here every amplitude stays
within $\sqrt{626} < 26$ for all time, as `amplitude_bound`
says of any state in the ball the decider establishes below.

-/

/-- The enstrophy identity for the compiled field. -/
theorem enstrophy_rate (x : Point 12) :
    (∑ i, 2 * x i * Gimle.Forseti.Nonlinear.field Gimle.Forseti.Examples.GalerkinNS.B2.compiled x i) =
      -2 * (1 / 50 : ℝ) * (x 0 * x 0 + (4 / 1 : ℝ) * x 1 * x 1 + (5 / 1 : ℝ) * x 2 * x 2 + (2 / 1 : ℝ) * x 3 * x 3 + x 4 * x 4 + (2 / 1 : ℝ) * x 5 * x 5 + (5 / 1 : ℝ) * x 6 * x 6 + (8 / 1 : ℝ) * x 7 * x 7 + (5 / 1 : ℝ) * x 8 * x 8 + (4 / 1 : ℝ) * x 9 * x 9 + (5 / 1 : ℝ) * x 10 * x 10 + (8 / 1 : ℝ) * x 11 * x 11) + 2 * (1 / 1 : ℝ) * x 5 := by
  rw [Gimle.Forseti.Examples.GalerkinNS.B2.field_eq]
  exact Gimle.Forseti.Examples.GalerkinNS.B2.enstrophy_identity x

/-- The laminar state's enstrophy, the least trappable level. -/
theorem laminar_enstrophy : (1 / 1 : ℝ) ^ 2 / (4 * (1 / 50) ^ 2) = 625 / 1 := by
  norm_num

/-- The enstrophy certificate, checked for the compiled field: the gap is a sum of squares. -/
theorem enstrophy_certificate_here (x : Point 12) :
    Gimle.Forseti.Examples.GalerkinNS.B2.trappingZ.alpha * (Gimle.Forseti.Examples.GalerkinNS.B2.trappingZ.inner - Gimle.Forseti.Examples.GalerkinNS.B2.trappingZ.energy x) - Gimle.Forseti.Examples.GalerkinNS.B2.trappingZ.rate (Gimle.Forseti.Nonlinear.field Gimle.Forseti.Examples.GalerkinNS.B2.compiled) x =
      (2 * (1 / 50) : ℝ) * (x 5 - 25 / 1) ^ 2 + (3 / 25 : ℝ) * x 1 ^ 2 + (4 / 25 : ℝ) * x 2 ^ 2 + (1 / 25 : ℝ) * x 3 ^ 2 + (4 / 25 : ℝ) * x 6 ^ 2 + (7 / 25 : ℝ) * x 7 ^ 2 + (4 / 25 : ℝ) * x 8 ^ 2 + (3 / 25 : ℝ) * x 9 ^ 2 + (4 / 25 : ℝ) * x 10 ^ 2 + (7 / 25 : ℝ) * x 11 ^ 2 := by
  exact Gimle.Forseti.Examples.GalerkinNS.B2.certificateZ x

/-- In the enstrophy ball every amplitude is bounded: $a_k^2 \le Z \le 626$. -/
theorem amplitude_bound (x : Point 12) (h : Gimle.Forseti.Examples.GalerkinNS.B2.enstrophy x ≤ 626) (i : Fin 12) :
    |x i| ≤ 26 := by
  rw [Gimle.Forseti.Examples.GalerkinNS.B2.enstrophy_eq_trappingZ, Gimle.Forseti.Examples.GalerkinNS.B2.enstrophy_eq_family] at h
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
so it cannot establish the requested energy bound $150$.
-/

/-- **Only two diagonal invariants.** Every weighting for which this member's
triads are lossless is a combination of $1/\lambda$ and $1$. -/
theorem only_two (w : Fin 12 → ℝ)
    (h0 : w 0 * (-3 / 20) + w 2 * (-1 / 4) + w 3 * (2 / 5) = 0)
    (h1 : w 0 * (-1 / 4) + w 4 * (1 / 4) = 0)
    (h2 : w 0 * (1 / 4) + w 4 * (-1 / 4) = 0)
    (h3 : w 0 * (3 / 20) + w 5 * (-2 / 5) + w 6 * (1 / 4) = 0)
    (h4 : w 0 * (-3 / 40) + w 7 * (-4 / 5) + w 8 * (7 / 8) = 0)
    (h5 : w 0 * (-1 / 20) + w 8 * (-3 / 4) + w 9 * (4 / 5) = 0)
    (h6 : w 0 * (1 / 20) + w 9 * (-4 / 5) + w 10 * (3 / 4) = 0)
    (h7 : w 0 * (3 / 40) + w 10 * (-7 / 8) + w 11 * (4 / 5) = 0)
    (h8 : w 1 * (-4 / 5) + w 2 * (3 / 4) + w 4 * (1 / 20) = 0)
    (h9 : w 3 * (1 / 4) + w 5 * (-1 / 4) = 0)
    (h10 : w 1 * (4 / 5) + w 4 * (-1 / 20) + w 6 * (-3 / 4) = 0)
    (h11 : w 1 * (-1 / 4) + w 9 * (1 / 4) = 0)
    (h12 : w 8 * (-1 / 10) + w 10 * (1 / 10) = 0)
    (h13 : w 1 * (1 / 4) + w 9 * (-1 / 4) = 0)
    (h14 : w 2 * (-7 / 8) + w 4 * (3 / 40) + w 7 * (4 / 5) = 0)
    (h15 : w 2 * (-9 / 20) + w 8 * (9 / 20) = 0)
    (h16 : w 2 * (1 / 10) + w 6 * (-1 / 10) = 0)
    (h17 : w 3 * (-2 / 5) + w 4 * (3 / 20) + w 8 * (1 / 4) = 0)
    (h18 : w 3 * (-1 / 4) + w 5 * (1 / 4) = 0)
    (h19 : w 6 * (9 / 20) + w 10 * (-9 / 20) = 0)
    (h20 : w 4 * (-3 / 20) + w 5 * (2 / 5) + w 10 * (-1 / 4) = 0)
    (h21 : w 4 * (-3 / 40) + w 6 * (7 / 8) + w 11 * (-4 / 5) = 0) :
    ∃ α β : ℝ, w 0 = α * (1 / 1) + β ∧
      w 1 = α * (1 / 4) + β ∧
      w 2 = α * (1 / 5) + β ∧
      w 3 = α * (1 / 2) + β ∧
      w 4 = α * (1 / 1) + β ∧
      w 5 = α * (1 / 2) + β ∧
      w 6 = α * (1 / 5) + β ∧
      w 7 = α * (1 / 8) + β ∧
      w 8 = α * (1 / 5) + β ∧
      w 9 = α * (1 / 4) + β ∧
      w 10 = α * (1 / 5) + β ∧
      w 11 = α * (1 / 8) + β := by
  exact Gimle.Forseti.Examples.GalerkinNS.B2.only_two_diagonal w h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21


/-!
## Inspect the decided trajectory contracts {fold}

The queries certify energy bound $313$,
and enstrophy bound $626$, from the all-ones start at time zero. Energy
bound $1$ is refuted; $E \le 150$ and $Z \le 600$ remain unknown.
Unknown requests may have no claim card, so claim counts do not list every
unresolved query.

Existence for all time, uniqueness and the ball come from the library's general
trapping theorem, the same one that traps the Lorenz system (`Lorenz.lean`): clamp the field to
a box, solve on every $[0, n]$, glue, and fence with the strict decrease at the
ball's boundary. Every claim below is decided against the compiled circuit.
-/


/-!
### Inspect the energy bound of 313 {fold}

The query certifies existence, uniqueness and $0 \le E \le 313$ for
all time from the all-ones start.
-/

-- @decide in_ball : trajectory ns-b2 from (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1) at 0 observe E always : E >= 0 and E <= 313

namespace DecidedShared_eb9ca2106187

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 12 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 15 := ⟨12, by decide⟩

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.GalerkinNS.B2.evolution.states.map (·.initialId) = ["initial-a01", "initial-a02", "initial-a1m2", "initial-a1m1", "initial-a10", "initial-a11", "initial-a12", "initial-a2m2", "initial-a2m1", "initial-a20", "initial-a21", "initial-a22"] ∧
  (Gimle.Forseti.Examples.GalerkinNS.B2.body.observations.get forsetiObservation).port.id =
    "obs-e" ∧
  Gimle.Forseti.Examples.GalerkinNS.B2.evolution.axis.id = "time"

end DecidedShared_eb9ca2106187

namespace Decided_in_ball

open DecidedShared_eb9ca2106187

example : @forsetiTime = @DecidedShared_eb9ca2106187.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_eb9ca2106187.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_eb9ca2106187.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_eb9ca2106187.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (313) 1))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["E"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (313) 1)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.B2.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- E is output 12 of the compiled circuit, the port obs-e; the input's initial wires (initial-a01, initial-a02, initial-a1m2, initial-a1m1, initial-a10, initial-a11, initial-a12, initial-a2m2, initial-a2m1, initial-a20, initial-a21, initial-a22) start at (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-b2 interpretation continuous-real obligation contract start time = 0 initial initial-a01 = 1, initial-a02 = 1, initial-a10 = 1, initial-a11 = 1, initial-a12 = 1, initial-a1m1 = 1, initial-a1m2 = 1, initial-a20 = 1, initial-a21 = 1, initial-a22 = 1, initial-a2m1 = 1, initial-a2m2 = 1 observe obs-e as E always : E >= 0 and E <= 313 -/
theorem in_ball :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.B2.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 12),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 12; E ≥ 0 ∧ E ≤ 313) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.B2.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.B2.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.B2.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.B2.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.B2.energyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.B2.energy_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (313) 1) : ℚ) : ℝ) = 313 := by norm_num [Rat.mkRat_eq_div]
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

The initial energy is $91/20>1$. A checked refutation is retained
beside the notebook; the false positive claim deliberately uses `sorry`.
-/

end Decided_in_ball


-- @decide below_one : trajectory ns-b2 from (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1) at 0 observe E always : E <= 1

namespace Decided_below_one

open DecidedShared_eb9ca2106187

example : @forsetiTime = @DecidedShared_eb9ca2106187.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_eb9ca2106187.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_eb9ca2106187.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_eb9ca2106187.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1)))))

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.B2.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- E is output 12 of the compiled circuit, the port obs-e; the input's initial wires (initial-a01, initial-a02, initial-a1m2, initial-a1m1, initial-a10, initial-a11, initial-a12, initial-a2m2, initial-a2m1, initial-a20, initial-a21, initial-a22) start at (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1) at time = 0. The trajectory decider refuted it. Goal (trajectory): trajectory ns-b2 interpretation continuous-real obligation contract start time = 0 initial initial-a01 = 1, initial-a02 = 1, initial-a10 = 1, initial-a11 = 1, initial-a12 = 1, initial-a1m1 = 1, initial-a1m2 = 1, initial-a20 = 1, initial-a21 = 1, initial-a22 = 1, initial-a2m1 = 1, initial-a2m2 = 1 observe obs-e as E always : E <= 1 -/
theorem below_one :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.B2.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 12),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 12; E ≤ 1) := by
  sorry

theorem below_one_refuted : ¬ (have circuit := Gimle.Forseti.Examples.GalerkinNS.B2.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 12),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 12; E ≤ 1)) := by
  have refuted : forsetiIdentities ∧ ¬ forsetiContract := by
    unfold forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    intro contract
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.B2.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.B2.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.B2.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.B2.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.B2.energyIndex := rfl
    rw [time, init, obs] at contract
    obtain ⟨state, realized⟩ := Gimle.Forseti.Examples.GalerkinNS.B2.compiled_exists
    have start : state Gimle.Forseti.Examples.GalerkinNS.B2.evolution.time.start = Gimle.Forseti.Examples.GalerkinNS.B2.compiled.initial := by unfold Gimle.Asgard.Model.ContinuousModel.Realizes Gimle.Asgard.Model.ContinuousModel.feedback at realized; exact ((Gimle.Forseti.Trajectory.close_rel _ _ _ _ _ _).mp realized).2.1
    have bounded := contract.holds _ Gimle.Forseti.Examples.GalerkinNS.B2.declared_input_admitted _ ⟨state, (Gimle.Forseti.Examples.GalerkinNS.B2.feedback_reads _ Gimle.Forseti.Examples.GalerkinNS.B2.declared_input_admitted state).mpr realized, rfl⟩ Gimle.Forseti.Examples.GalerkinNS.B2.evolution.time.start (by simp [Gimle.Asgard.Dynamics.TimeDomain.domain])
    simp only at bounded
    rw [start, Gimle.Forseti.Examples.GalerkinNS.B2.energy_at_initial] at bounded
    have witness : forsetiPost.holds (fun i => (((fun _ : Fin 1 => (mkRat (91) 20)) i : ℚ) : ℝ)) := by convert bounded using 2; norm_num [Rat.mkRat_eq_div]
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
### Compare unresolved energy with certified enstrophy {fold}

The request $E \le 150$ remains unknown. The next request certifies
existence, uniqueness and $0 \le Z \le 626$ from the stated start,
supporting the amplitude bound above. The later request $Z \le 600$
also remains unknown.
-/

end Decided_below_one


-- @decide below_150 : trajectory ns-b2 from (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1) at 0 observe E always : E <= 150

-- @decide in_enstrophy_ball : trajectory ns-b2 from (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1) at 0 observe Z always : Z >= 0 and Z <= 626

namespace DecidedShared_2983651b73e2

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 12 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 15 := ⟨13, by decide⟩

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.GalerkinNS.B2.evolution.states.map (·.initialId) = ["initial-a01", "initial-a02", "initial-a1m2", "initial-a1m1", "initial-a10", "initial-a11", "initial-a12", "initial-a2m2", "initial-a2m1", "initial-a20", "initial-a21", "initial-a22"] ∧
  (Gimle.Forseti.Examples.GalerkinNS.B2.body.observations.get forsetiObservation).port.id =
    "obs-z" ∧
  Gimle.Forseti.Examples.GalerkinNS.B2.evolution.axis.id = "time"

end DecidedShared_2983651b73e2

namespace Decided_in_enstrophy_ball

open DecidedShared_2983651b73e2

example : @forsetiTime = @DecidedShared_2983651b73e2.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_2983651b73e2.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_2983651b73e2.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_2983651b73e2.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (626) 1))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["Z"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (626) 1)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.B2.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- Z is output 13 of the compiled circuit, the port obs-z; the input's initial wires (initial-a01, initial-a02, initial-a1m2, initial-a1m1, initial-a10, initial-a11, initial-a12, initial-a2m2, initial-a2m1, initial-a20, initial-a21, initial-a22) start at (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-b2 interpretation continuous-real obligation contract start time = 0 initial initial-a01 = 1, initial-a02 = 1, initial-a10 = 1, initial-a11 = 1, initial-a12 = 1, initial-a1m1 = 1, initial-a1m2 = 1, initial-a20 = 1, initial-a21 = 1, initial-a22 = 1, initial-a2m1 = 1, initial-a2m2 = 1 observe obs-z as Z always : Z >= 0 and Z <= 626 -/
theorem in_enstrophy_ball :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.B2.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 12),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 15, circuit.Rel time u y →
        ∀ t ≥ 0, have Z := y t 13; Z ≥ 0 ∧ Z ≤ 626) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.B2.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.B2.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.B2.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.B2.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.B2.enstrophyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.B2.enstrophy_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (626) 1) : ℚ) : ℝ) = 626 := by norm_num [Rat.mkRat_eq_div]
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
not proofs. The requests $E \le 150$ and $Z \le 600$ remain unknown;
their absence from claim counts does not make them settled.
-/

end Decided_in_enstrophy_ball


-- @decide enstrophy_below_600 : trajectory ns-b2 from (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1) at 0 observe Z always : Z <= 600

#print axioms triad_lossless
#print axioms energy_rate
#print axioms laminar_energy
#print axioms certificate_here
#print axioms is_family_member
#print axioms every_member
#print axioms enstrophy_rate
#print axioms laminar_enstrophy
#print axioms enstrophy_certificate_here
#print axioms amplitude_bound
#print axioms only_two

end Notebook.NSB2
