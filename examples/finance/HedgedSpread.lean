import Mathlib
import Gimle.Forseti.Syntax.Certificate
import Gimle.Forseti.Examples.HedgedSpreadContract

/-!
# A stress test that covers every path

A trading book is stress-tested against a handful of chosen scenarios, and its
tail is estimated by sampling a few thousand shock paths. Either way, whatever
the scenarios or the sample did not contain is not in the report, and the paths
most likely to be missing are exactly the awkward ones: shocks that turn at the
wrong moment, that lean on the book just as the hedge is catching up. This
notebook does the other thing. For a small hedged book it proves that the
exposure never breaches its limit for **every** continuous shock inside a band,
for all time — not for the paths that were drawn, but for all of them, the
adversarial ones included. It does not say how bad the worst path is, only
that none breaches the limit; and it shows, honestly, what the same machinery
does not settle.

The book is a position on a spread that reverts to its mean, hedged with a
lag. Writing $s$ for the mark of the position in units of the desk's exposure
limit (so the limit is $|s| = 1$, and a breach is $|s| > 1$), $h$ for the
hedging flow the desk is still putting on, and $d$ for the market shock,

$$ s' = -s - h + d, \qquad h' = s - h, \qquad |d(t)| \le 1 \text{ for all } t \ge 0, $$

from a flat book $s(0) = h(0) = 0$. The term $-s$ is the spread's reversion to
its mean; $-h$ is the hedging flow offsetting the position; $h' = s - h$ is the
hedge following the exposure with a first-order lag of one time unit; and the
band $|d| \le 1$ is the stress scenario, one limit's worth of shock per unit of
time, in any continuous pattern whatever. The model is stylised and linear. The
shock is a *declared driver* of the compiled model, not a parameter: it may
vary in time, and nothing is assumed about it beyond continuity on $t \ge 0$
and the band. The library's word for a shock with that continuity is
*admitted*.

We watch two things: the exposure $s$ itself, and the quadratic

$$ V = s^2 + h^2, $$

the squared distance of the book from flat. The library calls it `energy`, the
usual name for such a quadratic; here it is a risk gauge, and the number $1$
is its budget.

**Proved.** For every continuous shock with $|d| \le 1$: a trajectory exists
for all $t \ge 0$, is unique, and satisfies $|s| \le 1$ throughout — the limit
is never breached on any path — and $0 \le V \le 1$. The mathematics is the
library's: existence, uniqueness and the invariant are hand proofs there. The
trajectory decider checks that each claim is an instance of the named contract
and that its certificate replays without the solver. A calmer market,
$|d| \le 1/2$, is decided too — but only against the same limit $1$: the
decider has one contract, at $B = 1$, and cannot see that the bound shrinks
with the band. The hand theorem at the end can.

**Refuted.** By the decider: $V \ge 1/4$ at all times — a deliberately false
claim, to show the refutation route — fails at the start, where the book is
flat and $V = 0$; Lean checks that witness. By hand, below, from a closed form
the library proves for constant shocks: inside the band, $1/2$ is *not* a bound
for the exposure (the constant shock $d = 1$ takes $s$ to
$1/2 + e^{-\pi/2}/2 \approx 0.60$ at $t = \pi/2$), and the band cannot be
dropped (the admitted but unbanded shock $d = 3$ takes $s$ to
$3/2 + 3e^{-\pi/2}/2 > 1$). The second is the non-vacuity check: without a
band, no linear book has a bound.

**Unknown.** $s \le 1/2$ for all $t \ge 0$ under the band. It is false — the
constant shock just mentioned passes $1/2$ — but the decider has two moves: the
named contract, which proves only the bound $1$, and the start, which does not
refute $1/2$. It says so rather than guess, and the hand proof below settles
it.

**Not claimed.** Anything probabilistic. The band is an assumption about the
shock, not a distribution over shocks, and nothing here says how likely any
path is. Nothing about returns, profit-and-loss distributions or value at
risk; nothing about other starting books, other reversion or lag rates, or
shocks outside the band. Nothing about shocks that jump: a gap move is not
continuous, so it is not admitted, and the bound is not extended to it here.
The model is the smallest one that shows the point: two states, one shock, one
quadratic.

## The book, as Lean reads it

The equations are declared once, in Asgard's source language, and compiled by
its verified compiler to a circuit over the coordinates $[d, s, h]$ — the
driver first, then the states. Lean reads the compiled right-hand sides off
that circuit (`rates_expressions` in the library) and proves them equal to a
linear operator plus the shock on the first row (`field_forced`); the identity
below is stated against the compiled rows themselves.

No simulation appears in this notebook, deliberately. A run would have to pick
one shock path, and the picture would quietly suggest that path is typical.
The one path worth looking at — the constant shock — Lean has exactly, further
down.
-/
namespace Notebook.HedgedSpread
open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory
open Gimle.Forseti.Examples.HedgedSpread Gimle.Forseti.Examples.HedgedSpreadContract

/-!
## Why the gauge cannot exceed one

Along any solution, the chain rule gives $V' = 2ss' + 2hh'$. Substituting the
equations,

$$ V' = 2s(-s - h + d) + 2h(s - h) = -2(s^2 + h^2) + 2sd. $$

The cross terms $-2sh$ and $+2hs$ cancel — read loosely, what the hedge gains
the exposure loses; precisely, the coupling matrix is skew-symmetric. That
cancellation is the whole mechanism: it is what lets a single quadratic see
both states at once. Lean checks the identity against the two compiled rows.
-/

/-- Along the compiled field at `[d, s, h]`, the gauge's rate is `-2V + 2sd`:
the coupling terms cancel. -/
theorem budget_rate (d : Point width) (x : Point states) :
    2 * x (0 : Fin 2) * (compiled.rates.expressions (0 : Fin 2)).eval (pointAppend d x) +
      2 * x (1 : Fin 2) * (compiled.rates.expressions (1 : Fin 2)).eval (pointAppend d x) =
      -2 * energy x + 2 * x (0 : Fin 2) * d dIndex := by
  rw [field_forced, field_forced, rate_zero (x := x), rate_one (x := x)]
  simp only [energy]
  ring

/-!
Inside the band $d^2 \le 1$, so $(s - d)^2 + h^2 + (1 - d^2) \ge 0$, which
rearranges to

$$ V' \le 1 - V. $$

So $e^{t}(V - 1)$ is non-increasing along every path. It starts at $-1$, so
$V \le 1 - e^{-t}$ for all $t \ge 0$: in particular $V \le 1$, hence
$|s| \le 1$. The argument never asks what the shock does next: the inequality
holds at every state and every admitted shock value, so it holds along every
path. That is the step a sampled stress test cannot take.
-/

/-- The algebraic leaf: inside the band the rate is at most `1 - V`. -/
theorem budget_leaf (s h d : ℝ) (hd : |d| ≤ 1) :
    -2 * (s ^ 2 + h ^ 2) + 2 * s * d ≤ 1 - (s ^ 2 + h ^ 2) := by
  simpa using storage_bound s h d 1 hd

/-!
## Existence, for every shock

A bound on trajectories is worth nothing if there are none. The library proves
that every admitted shock has a solution for all $t \ge 0$ by variation of
constants: the shock is continuous on $t \ge 0$, it is frozen at its start
value for negative times to make it continuous on the whole line, and the
forced linear system then has a global solution; uniqueness is the homogeneous
linear theorem applied to the difference of two solutions. The contract named
below bundles existence, uniqueness and the bound, and the decider proves
nothing about the exposure without all three.

## The claims, decided

Each claim is decided against the compiled circuit from the flat book, for
every admitted shock inside the band named by `within`. The block that follows
each directive is the decider's output, inserted as proposed and checked by
Lean as part of this file. First, the limit itself.
-/

-- @decide no_limit_breach : trajectory hedged-spread from (0, 0) at 0 within 1 observe s always : s >= -1 and s <= 1

namespace Decided_no_limit_breach

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 2 :=
  ![(((mkRat (0) 1) : ℚ) : ℝ), (((mkRat (0) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 2 := ⟨0, by decide⟩

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.add (.var ⟨0, by decide⟩) (.neg (.neg (.constant (mkRat (1) 1)))))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["s"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.add (.neg (.var ⟨0, by decide⟩)) (.neg (.constant (mkRat (1) 1))))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1)))))),
    forsetiPost⟩

def forsetiDriver0 : Fin (Gimle.Asgard.Model.DriverBinding.width Gimle.Forseti.Examples.HedgedSpread.drivers) :=
  ⟨0, by decide⟩

def forsetiDrivers : Gimle.Asgard.Dynamics.Signal (Gimle.Asgard.Model.DriverBinding.width Gimle.Forseti.Examples.HedgedSpread.drivers) → Prop :=
  fun d => Gimle.Forseti.Examples.HedgedSpread.evolution.Admitted Gimle.Forseti.Examples.HedgedSpread.drivers d ∧
    (∀ t ∈ forsetiTime.domain, |d t forsetiDriver0| ≤ (((mkRat (1) 1) : ℚ) : ℝ))

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.HedgedSpread.evolution.states.map (·.initialId) = ["initial-s", "initial-h"] ∧
  (Gimle.Forseti.Examples.HedgedSpread.body.observations.get forsetiObservation).port.id =
    "obs-s" ∧
  Gimle.Forseti.Examples.HedgedSpread.evolution.axis.id = "time" ∧
  List.ofFn (Gimle.Asgard.Model.DriverBinding.ids Gimle.Forseti.Examples.HedgedSpread.drivers) = ["driver-d"] ∧
  Gimle.Asgard.Model.index (Gimle.Asgard.Model.DriverBinding.ids Gimle.Forseti.Examples.HedgedSpread.drivers) "driver-d" = some forsetiDriver0

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.HedgedSpreadContract.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime forsetiDrivers
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- s is output 0 of the compiled circuit, the port obs-s; the input's initial wires (initial-s, initial-h) start at (0, 0) at time = 0. The input's driver wires (driver-d) are admitted, with |driver-d| ≤ 1. The trajectory decider proved it. Goal (trajectory): trajectory hedged-spread interpretation continuous-real obligation contract start time = 0 initial initial-h = 0, initial-s = 0 drivers driver-d within 1 observe obs-s as s always : s >= -1 and s <= 1 -/
theorem no_limit_breach :
    have circuit := Gimle.Forseti.Examples.HedgedSpreadContract.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (1 + 2),
      Gimle.Forseti.Examples.HedgedSpread.evolution.Admitted Gimle.Forseti.Examples.HedgedSpread.drivers
        (Gimle.Asgard.Dynamics.signalLeft u) →
      (∀ t ≥ 0, |Gimle.Asgard.Dynamics.signalLeft u t 0| ≤ 1) →
      Gimle.Asgard.Dynamics.signalRight u 0 = ![0, 0] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y →
        ∀ t ≥ 0, have s := y t 0; s ≥ -1 ∧ s ≤ 1) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract forsetiDrivers
    refine ⟨⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.HedgedSpread.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.HedgedSpread.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.HedgedSpread.compiled.initial := by rw [Gimle.Forseti.Examples.HedgedSpread.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.HedgedSpread.sIndex := rfl
    have drv : forsetiDriver0 = Gimle.Forseti.Examples.HedgedSpread.dIndex := rfl
    rw [time, init, obs, drv]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.HedgedSpreadContract.exposure_contract (fun _ admitted => ⟨⟨admitted.1.1, fun t within => (admitted.1.2 t within).trans (by norm_num [Rat.mkRat_eq_div])⟩, admitted.2⟩) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiContract) => bridge.mpr (show forsetiIdentities ∧ forsetiContract from root).2) ?_
  constructor
  · intro claim
    unfold forsetiContract
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at claim
    refine ⟨?_, ?_, ?_⟩ <;> set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc]
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).1
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).2.1
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).2.2
  · intro lane
    unfold forsetiContract at lane
    obtain ⟨realizable, unique, holds⟩ := lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at realizable unique holds ⊢
    exact fun u admit band start => ⟨realizable u ⟨admit, band, start⟩, unique u ⟨admit, band, start⟩, holds u ⟨admit, band, start⟩⟩

end Decided_no_limit_breach

/-!
The same contract, read for $V$: the gauge stays within its budget.
-/

-- @decide budget_band : trajectory hedged-spread from (0, 0) at 0 within 1 observe V always : V >= 0 and V <= 1

namespace Decided_budget_band

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 2 :=
  ![(((mkRat (0) 1) : ℚ) : ℝ), (((mkRat (0) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 2 := ⟨1, by decide⟩

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["V"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1)))))),
    forsetiPost⟩

def forsetiDriver0 : Fin (Gimle.Asgard.Model.DriverBinding.width Gimle.Forseti.Examples.HedgedSpread.drivers) :=
  ⟨0, by decide⟩

def forsetiDrivers : Gimle.Asgard.Dynamics.Signal (Gimle.Asgard.Model.DriverBinding.width Gimle.Forseti.Examples.HedgedSpread.drivers) → Prop :=
  fun d => Gimle.Forseti.Examples.HedgedSpread.evolution.Admitted Gimle.Forseti.Examples.HedgedSpread.drivers d ∧
    (∀ t ∈ forsetiTime.domain, |d t forsetiDriver0| ≤ (((mkRat (1) 1) : ℚ) : ℝ))

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.HedgedSpread.evolution.states.map (·.initialId) = ["initial-s", "initial-h"] ∧
  (Gimle.Forseti.Examples.HedgedSpread.body.observations.get forsetiObservation).port.id =
    "obs-v" ∧
  Gimle.Forseti.Examples.HedgedSpread.evolution.axis.id = "time" ∧
  List.ofFn (Gimle.Asgard.Model.DriverBinding.ids Gimle.Forseti.Examples.HedgedSpread.drivers) = ["driver-d"] ∧
  Gimle.Asgard.Model.index (Gimle.Asgard.Model.DriverBinding.ids Gimle.Forseti.Examples.HedgedSpread.drivers) "driver-d" = some forsetiDriver0

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.HedgedSpreadContract.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime forsetiDrivers
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- V is output 1 of the compiled circuit, the port obs-v; the input's initial wires (initial-s, initial-h) start at (0, 0) at time = 0. The input's driver wires (driver-d) are admitted, with |driver-d| ≤ 1. The trajectory decider proved it. Goal (trajectory): trajectory hedged-spread interpretation continuous-real obligation contract start time = 0 initial initial-h = 0, initial-s = 0 drivers driver-d within 1 observe obs-v as V always : V >= 0 and V <= 1 -/
theorem budget_band :
    have circuit := Gimle.Forseti.Examples.HedgedSpreadContract.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (1 + 2),
      Gimle.Forseti.Examples.HedgedSpread.evolution.Admitted Gimle.Forseti.Examples.HedgedSpread.drivers
        (Gimle.Asgard.Dynamics.signalLeft u) →
      (∀ t ≥ 0, |Gimle.Asgard.Dynamics.signalLeft u t 0| ≤ 1) →
      Gimle.Asgard.Dynamics.signalRight u 0 = ![0, 0] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y →
        ∀ t ≥ 0, have V := y t 1; V ≥ 0 ∧ V ≤ 1) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract forsetiDrivers
    refine ⟨⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.HedgedSpread.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.HedgedSpread.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.HedgedSpread.compiled.initial := by rw [Gimle.Forseti.Examples.HedgedSpread.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.HedgedSpread.vIndex := rfl
    have drv : forsetiDriver0 = Gimle.Forseti.Examples.HedgedSpread.dIndex := rfl
    rw [time, init, obs, drv]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.HedgedSpreadContract.energy_contract (fun _ admitted => ⟨⟨admitted.1.1, fun t within => (admitted.1.2 t within).trans (by norm_num [Rat.mkRat_eq_div])⟩, admitted.2⟩) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiContract) => bridge.mpr (show forsetiIdentities ∧ forsetiContract from root).2) ?_
  constructor
  · intro claim
    unfold forsetiContract
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at claim
    refine ⟨?_, ?_, ?_⟩ <;> set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc]
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).1
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).2.1
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).2.2
  · intro lane
    unfold forsetiContract at lane
    obtain ⟨realizable, unique, holds⟩ := lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at realizable unique holds ⊢
    exact fun u admit band start => ⟨realizable u ⟨admit, band, start⟩, unique u ⟨admit, band, start⟩, holds u ⟨admit, band, start⟩⟩

end Decided_budget_band

/-!
A calmer band, against the same limit — see *Any band* below for why the
decider cannot do better here.
-/

-- @decide calmer_market : trajectory hedged-spread from (0, 0) at 0 within 1/2 observe s always : s <= 1

namespace Decided_calmer_market

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 2 :=
  ![(((mkRat (0) 1) : ℚ) : ℝ), (((mkRat (0) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 2 := ⟨0, by decide⟩

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1)))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["s"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.add (.neg (.var ⟨0, by decide⟩)) (.neg (.constant (mkRat (1) 1))))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1)))))),
    forsetiPost⟩

def forsetiDriver0 : Fin (Gimle.Asgard.Model.DriverBinding.width Gimle.Forseti.Examples.HedgedSpread.drivers) :=
  ⟨0, by decide⟩

def forsetiDrivers : Gimle.Asgard.Dynamics.Signal (Gimle.Asgard.Model.DriverBinding.width Gimle.Forseti.Examples.HedgedSpread.drivers) → Prop :=
  fun d => Gimle.Forseti.Examples.HedgedSpread.evolution.Admitted Gimle.Forseti.Examples.HedgedSpread.drivers d ∧
    (∀ t ∈ forsetiTime.domain, |d t forsetiDriver0| ≤ (((mkRat (1) 2) : ℚ) : ℝ))

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.HedgedSpread.evolution.states.map (·.initialId) = ["initial-s", "initial-h"] ∧
  (Gimle.Forseti.Examples.HedgedSpread.body.observations.get forsetiObservation).port.id =
    "obs-s" ∧
  Gimle.Forseti.Examples.HedgedSpread.evolution.axis.id = "time" ∧
  List.ofFn (Gimle.Asgard.Model.DriverBinding.ids Gimle.Forseti.Examples.HedgedSpread.drivers) = ["driver-d"] ∧
  Gimle.Asgard.Model.index (Gimle.Asgard.Model.DriverBinding.ids Gimle.Forseti.Examples.HedgedSpread.drivers) "driver-d" = some forsetiDriver0

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.HedgedSpreadContract.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime forsetiDrivers
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- s is output 0 of the compiled circuit, the port obs-s; the input's initial wires (initial-s, initial-h) start at (0, 0) at time = 0. The input's driver wires (driver-d) are admitted, with |driver-d| ≤ 1/2. The trajectory decider proved it. Goal (trajectory): trajectory hedged-spread interpretation continuous-real obligation contract start time = 0 initial initial-h = 0, initial-s = 0 drivers driver-d within 1/2 observe obs-s as s always : s <= 1 -/
theorem calmer_market :
    have circuit := Gimle.Forseti.Examples.HedgedSpreadContract.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (1 + 2),
      Gimle.Forseti.Examples.HedgedSpread.evolution.Admitted Gimle.Forseti.Examples.HedgedSpread.drivers
        (Gimle.Asgard.Dynamics.signalLeft u) →
      (∀ t ≥ 0, |Gimle.Asgard.Dynamics.signalLeft u t 0| ≤ (1/2)) →
      Gimle.Asgard.Dynamics.signalRight u 0 = ![0, 0] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y →
        ∀ t ≥ 0, have s := y t 0; s ≤ 1) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract forsetiDrivers
    refine ⟨⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.HedgedSpread.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.HedgedSpread.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.HedgedSpread.compiled.initial := by rw [Gimle.Forseti.Examples.HedgedSpread.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.HedgedSpread.sIndex := rfl
    have drv : forsetiDriver0 = Gimle.Forseti.Examples.HedgedSpread.dIndex := rfl
    rw [time, init, obs, drv]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.HedgedSpreadContract.exposure_contract (fun _ admitted => ⟨⟨admitted.1.1, fun t within => (admitted.1.2 t within).trans (by norm_num [Rat.mkRat_eq_div])⟩, admitted.2⟩) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (1) 2) : ℚ) : ℝ) = (1/2) := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiContract) => bridge.mpr (show forsetiIdentities ∧ forsetiContract from root).2) ?_
  constructor
  · intro claim
    unfold forsetiContract
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at claim
    refine ⟨?_, ?_, ?_⟩ <;> set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc]
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).1
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).2.1
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).2.2
  · intro lane
    unfold forsetiContract at lane
    obtain ⟨realizable, unique, holds⟩ := lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at realizable unique holds ⊢
    exact fun u admit band start => ⟨realizable u ⟨admit, band, start⟩, unique u ⟨admit, band, start⟩, holds u ⟨admit, band, start⟩⟩

end Decided_calmer_market

/-!
A floor on $V$ fails where the book starts, flat: the decider finds the
witness and Lean checks it.
-/

-- @decide budget_quarter : trajectory hedged-spread from (0, 0) at 0 within 1 observe V always : V >= 1/4

namespace Decided_budget_quarter

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 2 :=
  ![(((mkRat (0) 1) : ℚ) : ℝ), (((mkRat (0) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 2 := ⟨1, by decide⟩

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.atom .ge (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 4)))))

def forsetiDriver0 : Fin (Gimle.Asgard.Model.DriverBinding.width Gimle.Forseti.Examples.HedgedSpread.drivers) :=
  ⟨0, by decide⟩

def forsetiDrivers : Gimle.Asgard.Dynamics.Signal (Gimle.Asgard.Model.DriverBinding.width Gimle.Forseti.Examples.HedgedSpread.drivers) → Prop :=
  fun d => Gimle.Forseti.Examples.HedgedSpread.evolution.Admitted Gimle.Forseti.Examples.HedgedSpread.drivers d ∧
    (∀ t ∈ forsetiTime.domain, |d t forsetiDriver0| ≤ (((mkRat (1) 1) : ℚ) : ℝ))

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.HedgedSpread.evolution.states.map (·.initialId) = ["initial-s", "initial-h"] ∧
  (Gimle.Forseti.Examples.HedgedSpread.body.observations.get forsetiObservation).port.id =
    "obs-v" ∧
  Gimle.Forseti.Examples.HedgedSpread.evolution.axis.id = "time" ∧
  List.ofFn (Gimle.Asgard.Model.DriverBinding.ids Gimle.Forseti.Examples.HedgedSpread.drivers) = ["driver-d"] ∧
  Gimle.Asgard.Model.index (Gimle.Asgard.Model.DriverBinding.ids Gimle.Forseti.Examples.HedgedSpread.drivers) "driver-d" = some forsetiDriver0

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.HedgedSpreadContract.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime forsetiDrivers
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- V is output 1 of the compiled circuit, the port obs-v; the input's initial wires (initial-s, initial-h) start at (0, 0) at time = 0. The input's driver wires (driver-d) are admitted, with |driver-d| ≤ 1. The trajectory decider refuted it. Goal (trajectory): trajectory hedged-spread interpretation continuous-real obligation contract start time = 0 initial initial-h = 0, initial-s = 0 drivers driver-d within 1 observe obs-v as V always : V >= 1/4 -/
theorem budget_quarter_refuted : ¬ (have circuit := Gimle.Forseti.Examples.HedgedSpreadContract.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (1 + 2),
      Gimle.Forseti.Examples.HedgedSpread.evolution.Admitted Gimle.Forseti.Examples.HedgedSpread.drivers
        (Gimle.Asgard.Dynamics.signalLeft u) →
      (∀ t ≥ 0, |Gimle.Asgard.Dynamics.signalLeft u t 0| ≤ 1) →
      Gimle.Asgard.Dynamics.signalRight u 0 = ![0, 0] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 2, circuit.Rel time u y →
        ∀ t ≥ 0, have V := y t 1; V ≥ 1/4)) := by
  have refuted : forsetiIdentities ∧ ¬ forsetiContract := by
    unfold forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel⟩, ?_⟩
    intro contract
    have time : forsetiTime = Gimle.Forseti.Examples.HedgedSpread.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.HedgedSpread.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.HedgedSpread.compiled.initial := by rw [Gimle.Forseti.Examples.HedgedSpread.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.HedgedSpread.vIndex := rfl
    rw [time, init, obs] at contract
    have zero : Gimle.Forseti.Examples.HedgedSpread.evolution.Admitted Gimle.Forseti.Examples.HedgedSpread.drivers (fun _ _ => 0) := Gimle.Forseti.Examples.HedgedSpreadContract.zero_admitted
    have admit : Gimle.Forseti.Trajectory.Initialized Gimle.Forseti.Examples.HedgedSpread.evolution.time forsetiDrivers (· = Gimle.Forseti.Examples.HedgedSpread.compiled.initial) (Gimle.Forseti.Examples.HedgedSpreadContract.withInitial fun _ _ => 0) := ⟨⟨by simpa [Gimle.Forseti.Examples.HedgedSpreadContract.withInitial] using zero, fun t _ => by simp [Gimle.Forseti.Examples.HedgedSpreadContract.withInitial] <;> norm_num [Rat.mkRat_eq_div]⟩, Gimle.Forseti.Examples.HedgedSpreadContract.constant_start _⟩
    obtain ⟨output, related⟩ := contract.realizable _ admit
    have origin : Gimle.Forseti.Examples.HedgedSpread.evolution.time.start = 0 := by simp [Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.HedgedSpread.evolution]
    have bounded := contract.holds _ admit output related Gimle.Forseti.Examples.HedgedSpread.evolution.time.start (by simp [Gimle.Asgard.Dynamics.TimeDomain.domain])
    simp only at bounded
    rw [origin, Gimle.Forseti.Examples.HedgedSpreadContract.output_at_start_v _ (Gimle.Forseti.Examples.HedgedSpreadContract.constant_start _) output related] at bounded
    have witness : forsetiPost.holds (fun i => (((fun _ : Fin 1 => (mkRat (0) 1)) i : ℚ) : ℝ)) := by convert bounded using 2; norm_num [Rat.mkRat_eq_div]
    rw [← Gimle.Forseti.Syntax.Formula.holdsQ_iff] at witness
    exact absurd witness (by decide +kernel)
  intro claim
  have forsetiCast0 : (((mkRat (1) 4) : ℚ) : ℝ) = (1/4) := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (0) 1) : ℚ) : ℝ) = 0 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiContract) => refuted.2 (bridge.mp claim)) ?_
  constructor
  · intro claim
    unfold forsetiContract
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at claim
    refine ⟨?_, ?_, ?_⟩ <;> set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc]
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).1
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).2.1
    · exact fun u ⟨admit, band, start⟩ => (claim u admit band start).2.2
  · intro lane
    unfold forsetiContract at lane
    obtain ⟨realizable, unique, holds⟩ := lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, forsetiDrivers, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at realizable unique holds ⊢
    exact fun u admit band start => ⟨realizable u ⟨admit, band, start⟩, unique u ⟨admit, band, start⟩, holds u ⟨admit, band, start⟩⟩

end Decided_budget_quarter

/-!
The last claim asks for half the limit. The decider leaves it unknown — its
one contract proves $1$, and the start does not refute $1/2$ — so no block
follows. The next section settles it by hand.
-/

-- @decide half_limit : trajectory hedged-spread from (0, 0) at 0 within 1 observe s always : s <= 1/2

/-!
## The constant shock, exactly

A random stress path wanders; it rarely leans on the book in one direction for
long. The constant shock does, and for it the library writes the solution down
exactly: under $d = c$,

$$ s(t) = \frac{c}{2} - \frac{c}{2}\,e^{-t}(\cos t - \sin t), \qquad h(t) = \frac{c}{2} - \frac{c}{2}\,e^{-t}(\cos t + \sin t). $$

The exposure spirals toward $c/2$ and overshoots it on the way: its first
peak is at $t = \pi/2$, where $s' = c\,e^{-t}\cos t$ vanishes and
$s = c/2 + (c/2)e^{-\pi/2}$, above the level it settles to. Two conclusions
follow. The first two theorems below are the shared witness: the unit shock is
admitted and has an output, and every realized output takes this value at the
peak — that is where the library's uniqueness theorem does its work, so the
closed form speaks for every realized output, not just a solution someone
wrote down. The next two draw the conclusions.
-/

/-- The constant shock `d = 1` is admitted and starts flat, so the book has an
output under it. -/
theorem unit_shock_realized :
    ∃ output, observed.Rel evolution.time (withInitial (constantDriver 1)) output := by
  exact realized _ (constant_start _) (by simpa [withInitial] using constant_admitted 1)

/-- Under `d = 1`, every realized exposure at its first peak `t = π/2` is
`1/2 + e^(-π/2)/2`. -/
theorem exposure_under_unit_shock (output)
    (related : observed.Rel evolution.time (withInitial (constantDriver 1)) output) :
    output (Real.pi / 2) sIndex = 1 / 2 + Real.exp (-(Real.pi / 2)) / 2 := by
  rw [constant_output 1 output related (Real.pi / 2) Real.pi_div_two_pos.le]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

/-- Inside the band, one half is not a bound: the one-sided claim `half_limit`
left unknown above is false, because the unit shock is admitted and its realized
exposure passes `1/2` at `t = π/2`. -/
theorem half_is_not_a_bound :
    ¬ Holds observed evolution.time admitted
      (Always evolution.time fun o => o sIndex ≤ 1 / 2) := by
  intro holds
  have admit : admitted (withInitial (constantDriver 1)) :=
    ⟨⟨by simpa [withInitial] using constant_admitted 1,
      fun t _ => by simp [withInitial, constantDriver]⟩, constant_start _⟩
  obtain ⟨output, related⟩ := unit_shock_realized
  have inDomain : Real.pi / 2 ∈ evolution.time.domain := by
    rw [domain_eq]
    exact Set.mem_Ici.2 Real.pi_div_two_pos.le
  have high : output (Real.pi / 2) sIndex ≤ 1 / 2 :=
    holds _ admit output related (Real.pi / 2) inDomain
  rw [exposure_under_unit_shock output related] at high
  linarith [Real.exp_pos (-(Real.pi / 2))]

/-- The band is doing the work: with the shock admitted but unbounded, the
limit fails under `d = 3`. -/
theorem band_needed :
    ¬ Holds observed evolution.time admittedOnly
      (Always evolution.time fun o => -1 ≤ o sIndex ∧ o sIndex ≤ 1) := by
  exact bound_needed

/-!
## Any band

Nothing in the argument used the number one. For a band $|d| \le B$ with
$B \ge 0$ (for a negative $B$ the band is empty and the statement vacuous), the
same quadratic gives $V \le B^2$ — the library's `energy_within` — and
$|s| \le B$: the exposure bound scales linearly with the stress scenario. The
decided `calmer_market` above is *not* this instance: it asked only $s \le 1$
under the half band and was proved through the contract at $B = 1$. `any_band`
is the whole family.
-/

/-- The contract at every band: `|d| ≤ B` keeps `|s| ≤ B`. -/
theorem any_band (B : ℝ) :
    Contract observed evolution.time (admittedWithin B)
      (Always evolution.time fun o => -B ≤ o sIndex ∧ o sIndex ≤ B) := by
  exact exposure_within B

/-!
## What is and is not in the picture

The proved bound has the right shape and not the right constant. The shape is
forced: the book is linear in the shock, so the worst exposure over the band
$|d| \le B$ is $\kappa B$ for one fixed $\kappa$, and the constant shock shows
$\kappa \ge 0.60$. The constant is loose: for a linear book $\kappa$ is the
$L^1$ norm of the response to an impulse,
$\int_0^\infty |e^{-t}\cos t|\,dt = \tfrac{1}{2} + \tfrac{e^{-\pi/2}}{1 - e^{-\pi}} \approx 0.717$,
approached by shocks that flip sign exactly when the response does — the
awkward paths of the opening paragraph — and reached by no continuous one.
That calculation is ours, not Lean's. Certifying any constant below $1$ in
this framework would need a sharper invariant than a single quadratic. That is
the next rung, not this one.
-/

#print axioms budget_rate
#print axioms budget_leaf
#print axioms unit_shock_realized
#print axioms exposure_under_unit_shock
#print axioms half_is_not_a_bound
#print axioms band_needed
#print axioms any_band

end Notebook.HedgedSpread
