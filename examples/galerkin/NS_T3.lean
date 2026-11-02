import Mathlib
import Gimle.Forseti.Syntax.Certificate
import Gimle.Forseti.Examples.GalerkinNS.T3
import Gimle.Forseti.Examples.GalerkinNS.T3Below12
import Gimle.Forseti.Examples.GalerkinNS.T3Below9

/-!
# A three-mode model: proved, refuted, or unresolved

**Scope: three-mode coefficient ODE only; no Navier–Stokes PDE claim.**

This exact finite model keeps three vorticity-mode amplitudes. The question is
simple: from the start $(1,1,1)$, can its energy be shown to remain below a
chosen bound for all time? The same pinned workflow gives three answers:
a checked proof, a checked time-zero counterexample, and an unresolved tighter
bound for which it found neither.

The sharp tube certificate was designed by an offline exact search and encoded
as rational data in the checked-in Forseti library. Glitnir selects that named
contract or runs a decision lane; Lean independently checks the resulting
proof or negation. Glitnir does not discover the tube in this notebook. The
projection that produced these three coefficients is taken as read.

The longer argument below derives the reusable family energy identity, adds
enstrophy control, and explains the degree-four trapping tube.

## The equations

Two-dimensional incompressible flow on the periodic square, in vorticity form,
keeps only the cosine modes $(1, 0)$, $(1, 1)$, $(2, 1)$ of the vorticity, with viscosity
$\nu = \tfrac{1}{10}$ and a constant force $f = 1$ on the mode $(1, 1)$.
Writing $a_k$ for the amplitude of $\cos(k \cdot x)$ and $\lambda_k = |k|^2$,
projecting the equations onto the modes gives, for every mode $k$ (the
projection is taken as read here; Lean checks everything from the
coefficients on),

$$ a_k' = -\nu \lambda_k a_k + f\,[k = (1,1)] + \sum_{\text{triads} \ni k} C_k\, a_P a_Q, $$

where $[k = (1,1)]$ is $1$ on the forced mode and $0$ otherwise, and a *triad*
$\{k, P, Q\}$ is three modes whose wavevectors, each taken with a sign, sum to
zero: $\pm k \pm P \pm Q = 0$. Its three coefficients are exact rationals fixed
by the geometry. This member has 1 triad.
In full, writing $a_{10}$ for $a_{(1,0)}$:

$$ \begin{aligned} a_{10}' &= - \tfrac{1}{10} a_{10} - \tfrac{3}{20} a_{11} a_{21} \\ a_{11}' &= 1 - \tfrac{1}{5} a_{11} + \tfrac{2}{5} a_{10} a_{21} \\ a_{21}' &= - \tfrac{1}{2} a_{21} - \tfrac{1}{4} a_{10} a_{11} \end{aligned} $$

**Proved.** From the start where every amplitude is $1$, a solution exists for
all $t \ge 0$, is unique, and its energy $E = \sum_k a_k^2/\lambda_k$ satisfies
$0 \le E \le 9$ throughout: below the laminar level
$\tfrac{25}{2}$, which no ball about the origin can pass, from a degree-four
tube around the focus the start approaches in simulation, trapped under a
decrease that holds on the set only (`below9_contract`); an ellipsoid with a
centre and cross terms gave $12$ first (`below12_contract`; the section
before the claims has both). Glitnir selects the named contract and Lean checks
the replayed proof. Its enstrophy $Z = \sum_k a_k^2$ satisfies
$0 \le Z \le 26$ throughout, by the same decider from a second named
contract, so every amplitude satisfies $|a_k| \le 6$ (`amplitude_bound`).

**Refuted.** $E \le 1$ for all $t \ge 0$: false at the start because
$\tfrac{17}{10} > 1$. The decision lane constructs a negation tied to the
initialized trajectory, and Lean checks it.

**Unresolved by this run.** For $E \le 8$ for all $t \ge 0$, this pinned,
bounded search found neither a replayable proof nor a checked counterexample.
The finite simulation stays below the threshold over $t \in [0,30]$; that does
not establish the forever claim. No reweighting
of the modes about the origin can close it: the energy and the enstrophy are
the only diagonal quadratics this member's triads conserve (`only_two` below),
and every closed trapping set that contains the origin contains the laminar
equilibrium, whose energy is $25/2$ — from the origin the flow runs along the
forced mode alone and tends to that state. No ellipsoid was found at
$E \le 10$; the tube that gives $9$ is of degree four, and at $8$ its
certificate has no room. This is search history, not a proof that no
certificate exists.

The thresholds were chosen to show the three response modes clearly; the
time-zero counterexample is deliberately simple.

**Not claimed.** Any Navier–Stokes PDE statement, checked PDE-to-ODE
derivation, convergence, truncation error, relation to the fluid, relation to
other truncations, or limit. Nothing about the shape of the flow beyond the
ball.

## The system, compiled

The equations are declared once, in Asgard's language, and compiled to a
circuit whose exact field Lean draws and reads:
-/
namespace Notebook.NST3
open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti Gimle.Forseti.Trajectory
  Gimle.Forseti.GalerkinNS Gimle.Forseti.Examples.GalerkinNS.T3

-- @view model Gimle.Forseti.Examples.GalerkinNS.T3.compiled
-- @evidence simulate Gimle.Forseti.Examples.GalerkinNS.T3.compiled (h := 1/100) (steps := 3000) (solver := rk4) (plane := a10, a21)

/-!
## Simulation: finite-time context, not proof

The run integrates the compiled field with RK4 in floating point over
$t \in [0,30]$. The energy
starts at $\tfrac{17}{10}$, peaks near $7.0$, and then settles at about $4.2$, a
steady state. That is evidence about this run and nothing more: it does not
enter any status. Every status above comes from an exact checked result or from
the bounded decision receipt, never from this plot.

## Derive the reusable energy bound {fold}

Triad cancellation gives the energy identity; a sum-of-squares certificate
then makes each energy ball with threshold above $25/2$ invariant. The same
argument applies to the finite family under its stated hypotheses. Sharper bounds for this
particular start need the later local trapping argument.

### Cancel the triad energy transfers {fold}

Weighting each mode's stored energy by $1/\lambda_k$ cancels the cubic
transfers within each triad. This yields the energy identity of the compiled
three-mode field.

The invariant is built from two kinds of piece. Each mode $k$ is a *storage
element*: its own squared amplitude obeys

$$ (a_k^2)' = -2\nu\lambda_k a_k^2 + 2 f a_k\,[k = (1,1)] + \sum_{\text{triads} \ni k} 2 C_k\, a_k a_P a_Q. $$

Each triad is a *lossless three-port*: weight the three cubic flows it feeds
into its modes by $1/\lambda_k$ and they sum to zero, so a triad only moves
energy between its modes. Here is one triad of this member, checked as plain
arithmetic:
-/

/-- The triad $\{a_{(1,0)}, a_{(1,1)}, a_{(2,1)}\}$ with weights $1/\lambda$: its three energy flows cancel exactly, and so do its
three enstrophy flows, with weights $1$. -/
theorem triad_lossless :
    (1 : ℝ) * (-3/20) + (1/2 : ℝ) * (2/5) + (1/5 : ℝ) * (-1/4) = 0 ∧
    (-3/20 : ℝ) + (2/5) + (-1/4) = 0 := by
  constructor <;> norm_num

/-!
Summing the storage identities with the weights $1/\lambda_k$, every cubic
term cancels triad by triad, and what remains is the **energy identity**

$$ E' = -2\nu Z + f\, a_{(1,1)}, \qquad Z = \sum_k a_k^2, $$

which Lean checks for the compiled field by expanding both sides.
-/

/-- The energy identity for the compiled field. -/
theorem energy_rate (x : Point 3) :
    (∑ i, 2 * (![(1 / 1 : ℝ), (1 / 2 : ℝ), (1 / 5 : ℝ)] : Fin 3 → ℝ) i * x i * Gimle.Forseti.Nonlinear.field compiled x i) =
      -2 * (1 / 10 : ℝ) * (x 0 * x 0 + x 1 * x 1 + x 2 * x 2) + (1 / 1 : ℝ) * x 1 := by
  rw [field_eq]
  exact energy_identity x

/-!
### Turn the identity into a trapping ball {fold}

The certificate makes energy decrease above $25/2$. For a start inside
$E \le 13$, it supplies a trapping ball; this bound applies to the finite ODE
system, without a claim about the full PDE.

Since $Z \ge E$ (every $\lambda_k \ge 1$) and the forcing acts on one mode, the
energy identity gives a differential inequality with an explicit certificate:

$$ 2\nu\Big(\frac{f^2}{8\nu^2} - E\Big) - E' = \nu\Big(a_{(1,1)} - \frac{f}{2\nu}\Big)^2 + 2\nu \sum_{k \ne (1,1)} \Big(1 - \frac{1}{\lambda_k}\Big) a_k^2 \;\ge\; 0. $$

So $E$ decreases whenever it exceeds $f^2/(8\nu^2) = \tfrac{25}{2}$, and any ball
above that level traps the flow forever. The level is not an artefact of the
proof: the laminar state, with only the forced mode excited at
$a_{(1,1)} = f/(2\nu)$, is an equilibrium with exactly that energy, and the
trajectory from rest along the forced mode alone,
$a_{(1,1)}(t) = \tfrac{f}{2\nu}(1 - e^{-2\nu t})$ with every other mode at zero
(a single mode feeds no triad), climbs from $E = 0$ to it, so every smaller
ball is left.
That global ball gives the coarse level $13$. The decided initialized trajectory
below uses the stronger local tube certificate to reach $E \le 9$.
-/

/-- The laminar equilibrium's energy, the least trappable level. -/
theorem laminar_energy : (1 : ℝ) ^ 2 / (8 * (1/10) ^ 2) = 25/2 := by
  norm_num

/-- The certificate, checked for the compiled field: the gap is a sum of squares. -/
theorem certificate_here (x : Point 3) :
    trapping.alpha * (trapping.inner - trapping.energy x) - trapping.rate (Gimle.Forseti.Nonlinear.field compiled) x =
      (1 / 10 : ℝ) * (x 1 - 5 / 1) ^ 2 + (4 / 25 : ℝ) * x 2 ^ 2 := by
  exact certificate x

/-!
### Connect this system to the finite family {fold}

The compiled field is an instance of the family field. At this viscosity
and forcing, any family member satisfying the mode hypotheses has a unique
global trajectory inside each ball $E \le C$ with $C>25/2$, provided its
initial state is inside that ball.

The three notebooks prove three members. The library also proves the family:
for every finite list of nonzero modes, with the forcing on one of them that
equals $(1,1)$, every viscosity $\nu > 0$ and forcing $f$, the energy identity
and the certificate hold, and for every $C > f^2/(8\nu^2)$ the set $E \le C$ is
invariant: from a start inside it a solution exists for all $t \ge$ any start
time, is unique, and stays inside (`GalerkinNS.Family`). Such a list is a
Galerkin truncation when its modes are distinct up to sign; that reading, the
projection, is taken as read, and from the family field on everything is
Lean. Two claims tie this member to it: Lean restates the library's check
(`field_eq_family`) that its compiled field is the family field at its
modes, and the family theorem at this viscosity and forcing.
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
$|a_k| \le 6$ for every amplitude. Energy and enstrophy also span the diagonal
quadratic invariants conserved by these triads; this is a statement about
this finite system.

### Derive the enstrophy certificate {fold}

The triads conserve enstrophy as well as energy. Its dissipation identity
supplies a second trapping certificate, whose bound controls each amplitude.

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
theorem enstrophy_rate (x : Point 3) :
    (∑ i, 2 * x i * Gimle.Forseti.Nonlinear.field Gimle.Forseti.Examples.GalerkinNS.T3.compiled x i) =
      -2 * (1 / 10 : ℝ) * (x 0 * x 0 + (2 / 1 : ℝ) * x 1 * x 1 + (5 / 1 : ℝ) * x 2 * x 2) + 2 * (1 / 1 : ℝ) * x 1 := by
  rw [Gimle.Forseti.Examples.GalerkinNS.T3.field_eq]
  exact Gimle.Forseti.Examples.GalerkinNS.T3.enstrophy_identity x

/-- The laminar state's enstrophy, the least trappable level. -/
theorem laminar_enstrophy : (1 / 1 : ℝ) ^ 2 / (4 * (1 / 10) ^ 2) = 25 / 1 := by
  norm_num

/-- The enstrophy certificate, checked for the compiled field: the gap is a sum of squares. -/
theorem enstrophy_certificate_here (x : Point 3) :
    Gimle.Forseti.Examples.GalerkinNS.T3.trappingZ.alpha * (Gimle.Forseti.Examples.GalerkinNS.T3.trappingZ.inner - Gimle.Forseti.Examples.GalerkinNS.T3.trappingZ.energy x) - Gimle.Forseti.Examples.GalerkinNS.T3.trappingZ.rate (Gimle.Forseti.Nonlinear.field Gimle.Forseti.Examples.GalerkinNS.T3.compiled) x =
      (2 * (1 / 10) : ℝ) * (x 1 - 5 / 1) ^ 2 + (4 / 5 : ℝ) * x 2 ^ 2 := by
  exact Gimle.Forseti.Examples.GalerkinNS.T3.certificateZ x

/-- In the enstrophy ball every amplitude is bounded: $a_k^2 \le Z \le 26$. -/
theorem amplitude_bound (x : Point 3) (h : Gimle.Forseti.Examples.GalerkinNS.T3.enstrophy x ≤ 26) (i : Fin 3) :
    |x i| ≤ 6 := by
  rw [Gimle.Forseti.Examples.GalerkinNS.T3.enstrophy_eq_trappingZ, Gimle.Forseti.Examples.GalerkinNS.T3.enstrophy_eq_family] at h
  have := Gimle.Forseti.GalerkinNS.Family.mode_sq_le_enstrophy x i
  rw [abs_le]
  constructor <;> nlinarith

/-!
### Explain the limit of diagonal reweighting {fold}

Every diagonal weighting conserved by the triads is a combination of the
energy and enstrophy weights. A tighter bound for this start needs a different
trapping set; this does not exclude other kinds of invariants.

And these two are all there is. A weighting $w$ of the modes for which every
triad is lossless — one linear equation per triad — is a combination of
$1/\lambda$ and $1$ (`only_two`, a `linear_combination` of the triad equations
with multipliers the generator computed exactly). No reweighting of the modes
about the origin traps tighter than the energy and the enstrophy; a trapping
set for the energy bound left unknown above would have to be centred away from
the laminar line (the design study says how far that has been tried). The lens
$\{E \le C_E\} \cap \{Z \le C_Z\}$ is the region both balls give together.
-/

/-- **Only two diagonal invariants.** Every weighting for which this member's
triads are lossless is a combination of $1/\lambda$ and $1$. -/
theorem only_two (w : Fin 3 → ℝ)
    (h0 : w 0 * (-3 / 20) + w 1 * (2 / 5) + w 2 * (-1 / 4) = 0) :
    ∃ α β : ℝ, w 0 = α * (1 / 1) + β ∧
      w 1 = α * (1 / 2) + β ∧
      w 2 = α * (1 / 5) + β := by
  exact Gimle.Forseti.Examples.GalerkinNS.T3.only_two_diagonal w h0


/-!
## Sharpen the bound for this initial state {fold}

The ellipsoid gives $E \le 12$ and a quartic tube gives $E \le 9$ for the
start $(1,1,1)$. They exclude the laminar equilibrium by requiring decrease
only on the trapping set. The requested bound $E \le 8$ remains unknown.

Every set the global decrease can trap contains every equilibrium: at an
equilibrium the rate is zero, so $V' \le \alpha(C' - V)$ forces $V \le C'$ there.
The laminar state $(0, 5, 0)$ is an equilibrium (`laminar_equilibrium`), so no
such set, whatever its weights or centre, has $\max E$ below $\tfrac{25}{2}$. A
set that excludes it needs a decrease that holds *on the set only*: at a first
contact with the boundary the rate is still $\le \alpha(C' - C) < 0$, so the
set is never left (the library's `LocalTrapping`, by a barrier lemma).

This member has three equilibria: the laminar saddle and a mirror pair of
stable foci at $E \approx 4.22$ (an exact computation in the design study, not
a theorem); in simulation the start settles on one of them.

### Trap the trajectory in an ellipsoid {fold}

The ellipsoid contains the start, excludes the laminar point, and lies
inside $E \le 12$. Its local decrease certificate supplies the trapping
argument in the imported library.

A search (the design study's spike, task 196) found an ellipsoid
$V = (x - c)^\top P (x - c) \le 1$ with cross terms and a centre near that focus
that contains the start, excludes the laminar point ($V \approx 2.54$ there), and lies
inside $E \le 12$; on it the decrease holds by an explicit degree-four sum of
squares with a multiplier $\sigma \ge 0$: $\alpha(C' - V) - V' + \sigma(V - 1)$
is a sum of squares everywhere, so where $V \le 1$ the decrease follows. All of
it is rational and every identity is `ring`; the library states the contract
`below12_contract`, which the decider cited for $E \le 12$ until the tube below
superseded it; its own theorems are restated here.
-/

/-- The laminar state is an equilibrium of the compiled field, restated. -/
theorem laminar_is_equilibrium : field ![0, 5, 0] = 0 := by
  exact laminar_equilibrium

/-- The ellipsoid excludes it and holds the start, restated. -/
theorem ellipsoid_excludes_laminar : 1 < Gimle.Forseti.Examples.GalerkinNS.T3.V ![0, 5, 0] ∧
    Gimle.Forseti.Examples.GalerkinNS.T3.V ![1, 1, 1] < 1 := by
  exact ⟨laminar_outside, start_inside⟩

/-- Inside the ellipsoid the energy is at most `12`, restated. -/
theorem ellipsoid_below_twelve (x : Point 3) (hx : Gimle.Forseti.Examples.GalerkinNS.T3.V x ≤ 1) :
    energy x ≤ 12 := by
  exact contained x hx

/-!
### Tighten the bound with a quartic tube {fold}

The tube contains the same start and lies inside $E \le 9$. Its decrease
certificate holds on the set; numerical evidence suggesting $E \le 8$
does not certify that stronger bound.

Tighter than the ellipsoid: with the whole orbit from the start held inside,
the same search over a **degree-four** $V$ finds a thin tube around the focus,
inside $E \le 9$ (numerically $E \le 7.985$ on it; at $8$ the containment
certificate has no room), with the decrease on the set by a degree-six sum of
squares. The library takes a polynomial $V$ (`PolynomialTrapping`) and states
`below9_contract`; the decider cites it below (for $13$, $10$ and $12$ alike).
-/

/-- The tube excludes the laminar point and holds the start, restated. -/
theorem tube_excludes_laminar : 1 < Gimle.Forseti.Examples.GalerkinNS.T3.tubeV ![0, 5, 0] ∧
    Gimle.Forseti.Examples.GalerkinNS.T3.tubeV ![1, 1, 1] < 1 := by
  exact ⟨tube_laminar_outside, tube_start_inside⟩

/-- Inside the tube the energy is at most `9`, restated. -/
theorem tube_below_nine (x : Point 3) (hx : Gimle.Forseti.Examples.GalerkinNS.T3.tubeV x ≤ 1) :
    energy x ≤ 9 := by
  exact tube_contained x hx

/-!
## Inspect the decided trajectory contracts {fold}

The queries certify energy bounds $9$, $10$ and $12$, and enstrophy bound
$26$, for the stated start. The energy bound $1$ is refuted; energy bound
$8$ and enstrophy bound $20$ remain unknown. Unknown requests may have no
claim card, so the claim counts do not list every unresolved query.

Existence for all time, uniqueness and the sets come from the library's
trapping theorems: the ball from the general one that traps the Lorenz system
(`Lorenz.lean`), the ellipsoid and the tube from its variants with the
decrease on the set,
each by clamping the field to a box, solving on every $[0, n]$, gluing, and
fencing at the boundary. Every claim below is decided against the compiled
circuit.
-/

/-!
### Inspect the energy bound of nine {fold}

The query certifies existence, uniqueness and $0 \le E \le 9$ for all
time from $(1,1,1)$. The current decision uses the stronger tube contract.
-/

-- @decide in_ball : trajectory ns-t3 from (1, 1, 1) at 0 observe E always : E >= 0 and E <= 9
namespace Decided_in_ball

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 3 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 6 := ⟨3, by decide⟩

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (9) 1))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["E"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (9) 1)))))),
    forsetiPost⟩

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.GalerkinNS.T3.evolution.states.map (·.initialId) = ["initial-a10", "initial-a11", "initial-a21"] ∧
  (Gimle.Forseti.Examples.GalerkinNS.T3.body.observations.get forsetiObservation).port.id =
    "obs-e" ∧
  Gimle.Forseti.Examples.GalerkinNS.T3.evolution.axis.id = "time"

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.T3.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- E is output 3 of the compiled circuit, the port obs-e; the input's initial wires (initial-a10, initial-a11, initial-a21) start at (1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-t3 interpretation continuous-real obligation contract start time = 0 initial initial-a10 = 1, initial-a11 = 1, initial-a21 = 1 observe obs-e as E always : E >= 0 and E <= 9 -/
theorem in_ball :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.T3.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 3; E ≥ 0 ∧ E ≤ 9) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.T3.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.T3.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.T3.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.T3.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.T3.energyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.T3.below9_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (9) 1) : ℚ) : ℝ) = 9 := by norm_num [Rat.mkRat_eq_div]
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

end Decided_in_ball

namespace DecidedShared_5a37f797df5f

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 3 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 6 := ⟨3, by decide⟩

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.GalerkinNS.T3.evolution.states.map (·.initialId) = ["initial-a10", "initial-a11", "initial-a21"] ∧
  (Gimle.Forseti.Examples.GalerkinNS.T3.body.observations.get forsetiObservation).port.id =
    "obs-e" ∧
  Gimle.Forseti.Examples.GalerkinNS.T3.evolution.axis.id = "time"

end DecidedShared_5a37f797df5f



-- @decide below_one : trajectory ns-t3 from (1, 1, 1) at 0 observe E always : E <= 1
namespace Decided_below_one

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 3 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 6 := ⟨3, by decide⟩

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1)))))

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.GalerkinNS.T3.evolution.states.map (·.initialId) = ["initial-a10", "initial-a11", "initial-a21"] ∧
  (Gimle.Forseti.Examples.GalerkinNS.T3.body.observations.get forsetiObservation).port.id =
    "obs-e" ∧
  Gimle.Forseti.Examples.GalerkinNS.T3.evolution.axis.id = "time"

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.T3.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- E is output 3 of the compiled circuit, the port obs-e; the input's initial wires (initial-a10, initial-a11, initial-a21) start at (1, 1, 1) at time = 0. The trajectory decider refuted it. Goal (trajectory): trajectory ns-t3 interpretation continuous-real obligation contract start time = 0 initial initial-a10 = 1, initial-a11 = 1, initial-a21 = 1 observe obs-e as E always : E <= 1 -/
theorem below_one_refuted : ¬ (have circuit := Gimle.Forseti.Examples.GalerkinNS.T3.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 3; E ≤ 1)) := by
  have refuted : forsetiIdentities ∧ ¬ forsetiContract := by
    unfold forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    intro contract
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.T3.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.T3.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.T3.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.T3.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.T3.energyIndex := rfl
    rw [time, init, obs] at contract
    obtain ⟨state, realized⟩ := Gimle.Forseti.Examples.GalerkinNS.T3.compiled_exists
    have start : state Gimle.Forseti.Examples.GalerkinNS.T3.evolution.time.start = Gimle.Forseti.Examples.GalerkinNS.T3.compiled.initial := by unfold Gimle.Asgard.Model.ContinuousModel.Realizes Gimle.Asgard.Model.ContinuousModel.feedback at realized; exact ((Gimle.Forseti.Trajectory.close_rel _ _ _ _ _ _).mp realized).2.1
    have bounded := contract.holds _ Gimle.Forseti.Examples.GalerkinNS.T3.declared_input_admitted _ ⟨state, (Gimle.Forseti.Examples.GalerkinNS.T3.feedback_reads _ Gimle.Forseti.Examples.GalerkinNS.T3.declared_input_admitted state).mpr realized, rfl⟩ Gimle.Forseti.Examples.GalerkinNS.T3.evolution.time.start (by simp [Gimle.Asgard.Dynamics.TimeDomain.domain])
    simp only at bounded
    rw [start, Gimle.Forseti.Examples.GalerkinNS.T3.energy_at_initial] at bounded
    have witness : forsetiPost.holds (fun i => (((fun _ : Fin 1 => (mkRat (17) 10)) i : ℚ) : ℝ)) := by convert bounded using 2; norm_num [Rat.mkRat_eq_div]
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

end Decided_below_one



-- @decide below_10 : trajectory ns-t3 from (1, 1, 1) at 0 observe E always : E <= 10

namespace Decided_below_10

open DecidedShared_5a37f797df5f

example : @forsetiTime = @DecidedShared_5a37f797df5f.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_5a37f797df5f.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_5a37f797df5f.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_5a37f797df5f.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (10) 1)))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["E"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (9) 1)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.T3.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- E is output 3 of the compiled circuit, the port obs-e; the input's initial wires (initial-a10, initial-a11, initial-a21) start at (1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-t3 interpretation continuous-real obligation contract start time = 0 initial initial-a10 = 1, initial-a11 = 1, initial-a21 = 1 observe obs-e as E always : E <= 10 -/
theorem below_10 :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.T3.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 3; E ≤ 10) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.T3.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.T3.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.T3.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.T3.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.T3.energyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.T3.below9_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (10) 1) : ℚ) : ℝ) = 10 := by norm_num [Rat.mkRat_eq_div]
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
### Compare a certified bound with an unresolved one {fold}

The request $E \le 8$ remains unknown; the next request $E \le 12$ is
certified from the tube contract. The earlier ellipsoid argument explains
another route to $12$, but neither certificate settles $8$.
-/

end Decided_below_10


-- @decide below_8 : trajectory ns-t3 from (1, 1, 1) at 0 observe E always : E <= 8

-- @decide below_12 : trajectory ns-t3 from (1, 1, 1) at 0 observe E always : E <= 12

namespace Decided_below_12

open DecidedShared_5a37f797df5f

example : @forsetiTime = @DecidedShared_5a37f797df5f.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_5a37f797df5f.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_5a37f797df5f.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_5a37f797df5f.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (12) 1)))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["E"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (9) 1)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.T3.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- E is output 3 of the compiled circuit, the port obs-e; the input's initial wires (initial-a10, initial-a11, initial-a21) start at (1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-t3 interpretation continuous-real obligation contract start time = 0 initial initial-a10 = 1, initial-a11 = 1, initial-a21 = 1 observe obs-e as E always : E <= 12 -/
theorem below_12 :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.T3.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 3; E ≤ 12) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.T3.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.T3.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.T3.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.T3.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.T3.energyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.T3.below9_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[((mkRat (3) 1), (.constant (mkRat (1) 1)))]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (12) 1) : ℚ) : ℝ) = 12 := by norm_num [Rat.mkRat_eq_div]
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
### Inspect the enstrophy bound of twenty-six {fold}

The enstrophy contract certifies existence, uniqueness and $0 \le Z \le 26$
for all time from the stated start. This supports the amplitude bounds above;
the later request $Z \le 20$ remains unknown.
-/

end Decided_below_12


-- @decide in_enstrophy_ball : trajectory ns-t3 from (1, 1, 1) at 0 observe Z always : Z >= 0 and Z <= 26

namespace DecidedShared_05178f0d2091

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 3 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 6 := ⟨4, by decide⟩

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.GalerkinNS.T3.evolution.states.map (·.initialId) = ["initial-a10", "initial-a11", "initial-a21"] ∧
  (Gimle.Forseti.Examples.GalerkinNS.T3.body.observations.get forsetiObservation).port.id =
    "obs-z" ∧
  Gimle.Forseti.Examples.GalerkinNS.T3.evolution.axis.id = "time"

end DecidedShared_05178f0d2091

namespace Decided_in_enstrophy_ball

open DecidedShared_05178f0d2091

example : @forsetiTime = @DecidedShared_05178f0d2091.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_05178f0d2091.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_05178f0d2091.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_05178f0d2091.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (26) 1))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["Z"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (26) 1)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.T3.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- Z is output 4 of the compiled circuit, the port obs-z; the input's initial wires (initial-a10, initial-a11, initial-a21) start at (1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-t3 interpretation continuous-real obligation contract start time = 0 initial initial-a10 = 1, initial-a11 = 1, initial-a21 = 1 observe obs-z as Z always : Z >= 0 and Z <= 26 -/
theorem in_enstrophy_ball :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.T3.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y →
        ∀ t ≥ 0, have Z := y t 4; Z ≥ 0 ∧ Z ≤ 26) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.T3.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.T3.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.T3.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.T3.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.T3.enstrophyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.T3.enstrophy_contract (fun _ admitted => admitted) ?_
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

end Decided_in_enstrophy_ball


-- @decide enstrophy_below_20 : trajectory ns-t3 from (1, 1, 1) at 0 observe Z always : Z <= 20

/-!
## Scope and unresolved bounds

These are statements about the compiled three-mode ODE at the stated
viscosity, forcing and initial state. They do not establish an approximation
or limiting theorem for the Navier–Stokes PDE. Simulations and certificate
searches guide the questions but are not proofs. The requests $E \le 8$ and
$Z \le 20$ remain unknown; their absence from a section's claim counts does
not make them settled.
-/

#print axioms triad_lossless
#print axioms energy_rate
#print axioms laminar_energy
#print axioms laminar_is_equilibrium
#print axioms ellipsoid_excludes_laminar
#print axioms ellipsoid_below_twelve
#print axioms tube_excludes_laminar
#print axioms tube_below_nine
#print axioms certificate_here
#print axioms is_family_member
#print axioms every_member
#print axioms enstrophy_rate
#print axioms laminar_enstrophy
#print axioms enstrophy_certificate_here
#print axioms amplitude_bound
#print axioms only_two

end Notebook.NST3
