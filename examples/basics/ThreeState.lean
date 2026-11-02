import Mathlib
import Gimle.Forseti.Syntax.Certificate
import Gimle.Forseti.Examples.ThreeStateContract

/-!
# Does the energy of a damped three-state system stay bounded?

Three coupled states $x$, $y$, $z$ push each other around and are each damped:

$$ x' = -a x + y - z $$
$$ y' = -x - b y + z $$
$$ z' = x - y - c z $$

with damping $(a, b, c) = (\tfrac13, \tfrac12, 2)$, started from $(x, y, z) = (1, 2, -1)$
at time $t = 2$. We watch its energy $V = x^2 + y^2 + z^2$, which starts at $6$.

The coupling terms are skew-symmetric, so they only move energy between the
states; the damping is the only thing that changes $V$. Because every damping
coefficient is positive, that suggests the energy can never grow. This notebook turns that intuition into checked claims,
and shows where the intuition is not enough.

## From equations to a circuit

The system is written once, as Asgard equations, in
`Gimle.Asgard.Examples.ThreeState.body`:

- `dx := -a * x + y - z`
- `dy := -x - b * y + z`
- `dz := x - y - c * z`
- `V := sqx + sqy + sqz`, with `sqx := x ^ 2` and likewise for `y`, `z`
- `dissipation := -2 * (a * sqx + b * sqy + c * sqz)`

`asgard-lean` compiles that declaration into a circuit, `model`, and proves the
compilation faithful: `Gimle.Asgard.Examples.ThreeState.solves_iff_realizes`
says a signal solves the declared equations and initial condition exactly when
it is a trajectory of the compiled circuit. Every trajectory claim below is
about that compiled circuit, so it is about the equations as written, not about
a re-typed copy of them.

## What is modelled, and what is not

The claims are about the exact real solutions for $t \ge 2$, for this one
parameter triple and this one initial state, with no inputs driving the
system. They say nothing about other starts, other damping values, or
robustness to either, and the bound $6$ below is simply the initial energy.
Nothing here says anything about a discretized or rounded implementation, and
no simulation enters any claim's status.
-/

namespace Notebook.ThreeState
open Gimle.Asgard Gimle.Asgard.Examples.ThreeState

-- @view model Gimle.Asgard.Examples.ThreeState.model
-- @evidence simulate Gimle.Asgard.Examples.ThreeState.model (h := 1/100) (steps := 1200) (solver := rk4)

/-!
## What a simulation shows

The run above is a floating-point simulation of the compiled field, kept beside
the claims as evidence. Lean emits the field exactly, with the damping as the
rationals `1/3`, `1/2` and `2`. The run rounds to float64 only to integrate, and
the snapshot lists what it rounded: `1/3` and the step `1/100`; `1/2` and `2`
are exact in float64. It integrates with RK4 from $t = 2$ to $t = 14$.

The run shows the damping at work: all three states decay towards zero, and the
energy with them; it is below one by about $t = 3.6$, well inside the bound
the decay argument under "Does the energy stay above one?" gives. That is
evidence, not proof.
No claim's status reads it: a trajectory that agreed with a false claim would
prove nothing, and one that disagreed with a true claim would refute nothing.
-/

/-!
## The energy stays in its band

The first claim is the one the intuition predicts: for every $t \ge 2$ the
energy lies in $[0, 6]$, and the system has exactly one solution for $t \ge 2$
from this start.

The band itself is a forseti-lean theorem,
`Gimle.Forseti.Examples.ThreeStateContract.energy_contract`, proved by hand
once for this model. The decider's job is to recognise that the goal as written
is an instance of that theorem about this compiled circuit: it checks the
names, time, initial state and observation, and bridges the two
postconditions with an entailment certificate that Lean re-checks. Here that
bridge is trivial; it does real work when the bound asked for is weaker than
the contract's.

The claim reads as the property, about `ThreeStateContract.observed`: the
compiled loop followed by its compiled observations `[z, x, y, V]`. For every
input whose initial wires start at $(1, 2, -1)$, that circuit has an output, all its outputs agree for
$t \ge 2$, and on every output $V$ (output 3, the port `obs-v`) stays in
$[0, 6]$ for $t \ge 2$. Its proof first proves the decider's own root theorem,
`forsetiRoot`, over the generated definitions folded away below, then shows
that this statement is equivalent to the root's contract; Lean checks both.
-/

-- @decide energy_band : trajectory three-state interpretation continuous-real
--   obligation contract start time = 2 initial initial-x = 1, initial-y = 2,
--   initial-z = -1 observe obs-v as V always : V >= 0 and V <= 6

namespace DecidedShared_e390e59d2288

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (2) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 3 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (2) 1) : ℚ) : ℝ), (((mkRat (-1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 4 := ⟨3, by decide⟩

def forsetiIdentities : Prop :=
  Gimle.Asgard.Examples.ThreeState.evolution.states.map (·.initialId) = ["initial-x", "initial-y", "initial-z"] ∧
  ((Gimle.Asgard.Examples.ThreeState.body (1 / 3) (1 / 2) 2).observations.get forsetiObservation).port.id =
    "obs-v" ∧
  Gimle.Asgard.Examples.ThreeState.evolution.axis.id = "time"

end DecidedShared_e390e59d2288

namespace Decided_energy_band

open DecidedShared_e390e59d2288

example : @forsetiTime = @DecidedShared_e390e59d2288.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_e390e59d2288.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_e390e59d2288.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_e390e59d2288.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (6) 1))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["V"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (6) 1)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.ThreeStateContract.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- V is output 3 of the compiled circuit, the port obs-v; the input's initial wires (initial-x, initial-y, initial-z) start at (1, 2, -1) at time = 2. The trajectory decider proved it. Goal (trajectory): trajectory three-state interpretation continuous-real obligation contract start time = 2 initial initial-x = 1, initial-y = 2, initial-z = -1 observe obs-v as V always : V >= 0 and V <= 6 -/
theorem energy_band :
    have circuit := Gimle.Forseti.Examples.ThreeStateContract.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 2⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 2 = ![1, 2, -1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 2, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y →
        ∀ t ≥ 2, have V := y t 3; V ≥ 0 ∧ V ≤ 6) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Asgard.Examples.ThreeState.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Asgard.Examples.ThreeState.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Asgard.Examples.ThreeState.model.initial := by rw [Gimle.Asgard.Examples.ThreeState.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Asgard.Examples.ThreeState.energyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.ThreeStateContract.energy_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (6) 1) : ℚ) : ℝ) = 6 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (2) 1) : ℚ) : ℝ) = 2 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast3 : (((mkRat (-1) 1) : ℚ) : ℝ) = -1 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiContract) => bridge.mpr (show forsetiIdentities ∧ forsetiContract from root).2) ?_
  constructor
  · intro claim
    unfold forsetiContract
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, forsetiCast3, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at claim
    refine ⟨?_, ?_, ?_⟩ <;> set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, forsetiCast3, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc]
    · exact fun u start => (claim u start).1
    · exact fun u start => (claim u start).2.1
    · exact fun u start => (claim u start).2.2
  · intro lane
    unfold forsetiContract at lane
    obtain ⟨realizable, unique, holds⟩ := lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, forsetiCast3, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at realizable unique holds ⊢
    exact fun u start => ⟨realizable u start, unique u start, holds u start⟩

end Decided_energy_band


/-!
## Five is not a bound

It is tempting to tighten the bound because the energy decays. But a bound for
all $t \ge 2$ must hold at $t = 2$ too, and the trajectory starts at $V = 6$, so
"the energy is at most five for all $t \ge 2$" is false. The decider does not
merely fail to prove it; it refutes it with the initial state as a checked
witness.

Below, the claim is stated in the same form as the band, with `sorry` in
place of a proof: it is false, so it has none. That positive theorem remains
admitted and displays **Contains sorry**. The separate theorem
`energy_below_five_refuted` below proves its negation and is checked. A later
claim that used the admitted positive theorem would inherit its `sorryAx`
assumption; the checked refutation does not turn that positive claim into a proof.
-/

-- @decide energy_below_five : trajectory three-state interpretation
--   continuous-real obligation contract start time = 2 initial initial-x = 1,
--   initial-y = 2, initial-z = -1 observe obs-v as V always : V <= 5

namespace Decided_energy_below_five

open DecidedShared_e390e59d2288

example : @forsetiTime = @DecidedShared_e390e59d2288.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_e390e59d2288.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_e390e59d2288.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_e390e59d2288.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (5) 1)))))

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.ThreeStateContract.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- V is output 3 of the compiled circuit, the port obs-v; the input's initial wires (initial-x, initial-y, initial-z) start at (1, 2, -1) at time = 2. The trajectory decider refuted it. Goal (trajectory): trajectory three-state interpretation continuous-real obligation contract start time = 2 initial initial-x = 1, initial-y = 2, initial-z = -1 observe obs-v as V always : V <= 5 -/
theorem energy_below_five :
    have circuit := Gimle.Forseti.Examples.ThreeStateContract.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 2⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 2 = ![1, 2, -1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 2, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y →
        ∀ t ≥ 2, have V := y t 3; V ≤ 5) := by
  sorry

theorem energy_below_five_refuted : ¬ (have circuit := Gimle.Forseti.Examples.ThreeStateContract.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 2⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 2 = ![1, 2, -1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 2, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 4, circuit.Rel time u y →
        ∀ t ≥ 2, have V := y t 3; V ≤ 5)) := by
  have refuted : forsetiIdentities ∧ ¬ forsetiContract := by
    unfold forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    intro contract
    have time : forsetiTime = Gimle.Asgard.Examples.ThreeState.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Asgard.Examples.ThreeState.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Asgard.Examples.ThreeState.model.initial := by rw [Gimle.Asgard.Examples.ThreeState.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Asgard.Examples.ThreeState.energyIndex := rfl
    rw [time, init, obs] at contract
    obtain ⟨state, realized⟩ := Gimle.Forseti.Examples.ThreeState.compiled_exists
    have start : state Gimle.Asgard.Examples.ThreeState.evolution.time.start = Gimle.Asgard.Examples.ThreeState.model.initial := by unfold Gimle.Asgard.Model.ContinuousModel.Realizes Gimle.Asgard.Model.ContinuousModel.feedback at realized; exact ((Gimle.Forseti.Trajectory.close_rel _ _ _ _ _ _).mp realized).2.1
    have bounded := contract.holds _ Gimle.Forseti.Examples.ThreeStateContract.declared_input_admitted _ ⟨state, (Gimle.Forseti.Examples.ThreeStateContract.feedback_reads _ Gimle.Forseti.Examples.ThreeStateContract.declared_input_admitted state).mpr realized, rfl⟩ Gimle.Asgard.Examples.ThreeState.evolution.time.start (by simp [Gimle.Asgard.Dynamics.TimeDomain.domain])
    simp only at bounded
    rw [start, Gimle.Asgard.Examples.ThreeState.energy_at_initial] at bounded
    have witness : forsetiPost.holds (fun i => (((fun _ : Fin 1 => (mkRat (6) 1)) i : ℚ) : ℝ)) := by convert bounded using 2; norm_num [Rat.mkRat_eq_div]
    rw [← Gimle.Forseti.Syntax.Formula.holdsQ_iff] at witness
    exact absurd witness (by decide +kernel)
  intro claim
  have forsetiCast0 : (((mkRat (5) 1) : ℚ) : ℝ) = 5 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (2) 1) : ℚ) : ℝ) = 2 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast3 : (((mkRat (-1) 1) : ℚ) : ℝ) = -1 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ forsetiContract) => refuted.2 (bridge.mp claim)) ?_
  constructor
  · intro claim
    unfold forsetiContract
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, forsetiCast3, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at claim
    refine ⟨?_, ?_, ?_⟩ <;> set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, forsetiCast3, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc]
    · exact fun u start => (claim u start).1
    · exact fun u start => (claim u start).2.1
    · exact fun u start => (claim u start).2.2
  · intro lane
    unfold forsetiContract at lane
    obtain ⟨realizable, unique, holds⟩ := lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Trajectory.Realizable, Gimle.Forseti.Trajectory.Unique, Gimle.Forseti.Trajectory.Holds, Gimle.Forseti.Trajectory.Initialized, Gimle.Forseti.Trajectory.Always, Set.EqOn, Gimle.Asgard.Dynamics.TimeDomain.domain, Set.mem_Ici, forsetiTime, forsetiInitial, forsetiPost, forsetiObservation, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, true_and, forsetiCast0, forsetiCast1, forsetiCast2, forsetiCast3, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc] at realizable unique holds ⊢
    exact fun u start => ⟨realizable u start, unique u start, holds u start⟩

end Decided_energy_below_five


/-!
## Does the energy stay above one?

It does not, though nothing here checks that. The weakest damping is
$a = \tfrac13$, so $V' \le -\tfrac23 V$, and $V(t) \le 6 e^{-2(t-2)/3}$ drops below one for
every $t > 2 + \tfrac32 \ln 6 \approx 4.7$. That argument is ours, not Lean's.

The decider cannot settle it either way. A refutation needs a checked witness,
a time and state where $V < 1$, and it only tries the start, where $V = 6$. Nor
can it prove the claim: the only contract it has, $0 \le V \le 6$, does not imply
$V \ge 1$. Its answer is **unknown**, the correct answer for a checker: unknown
means "not decided here", never "true" and never "false". Because there is
nothing to check, it adds no claim to the notebook; the answer stays with the
directive below. Refuting it in Forseti would take that decay bound as a Lean
theorem about the model; it is not one yet.
-/

-- @decide energy_at_least_one : trajectory three-state interpretation
--   continuous-real obligation contract start time = 2 initial initial-x = 1,
--   initial-y = 2, initial-z = -1 observe obs-v as V always : V >= 1

/-!
## Why the energy cannot grow

Along a trajectory $V' = 2\langle x, f(x)\rangle$, where $f$ is the compiled field. The last
claim checks that this pairing is never positive, at any state, for the field
the compiler produced. `energy_pairing` in asgard-lean rewrites it as the
model's declared `dissipation := -2 * (a*sqx + b*sqy + c*sqz)`, and
`energyRate_value` gives that expression with the damping substituted; with
positive damping it is a negatively weighted sum of squares.

The prover agent proved it with ordinary Lean tactics, given one hint naming
the two lemmas. The band above was proved independently in forseti-lean, from
the same fact stated about the model's matrix; it does not use this claim.
-/

/-- $2\langle x, f(x)\rangle \le 0$ for the compiled field $f$: the energy rate is never positive. -/
theorem energy_rate_nonpositive (x : Gimle.Asgard.Point 3) :
    2 * ∑ i, x i * model.rates.circuit.run x i ≤ 0 := by
  rw [Gimle.Asgard.Examples.ThreeState.energy_pairing]
  rw [Gimle.Asgard.Examples.ThreeState.energyRate_value]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

end Notebook.ThreeState
