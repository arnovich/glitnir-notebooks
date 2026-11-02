import Mathlib
import Gimle.Forseti.Syntax.Certificate
import Gimle.Forseti.Examples.GalerkinNS.T3S

/-!
# A 3-mode truncation of Navier–Stokes at small forcing: the laminar line attracts

The same three cosine modes as `NS_T3.lean`, $(1, 0)$, $(1, 1)$, $(2, 1)$, with
the same force $f = 1$ on $(1, 1)$, but five times the viscosity:
$\nu = \tfrac12$ instead of $\tfrac{1}{10}$. The Grashof-type number $f/\nu^2$
drops from $100$ to $4$, and the flow changes character: at $\nu = \tfrac{1}{10}$
the laminar state is linearly unstable (numerically) and the simulated
trajectory settles elsewhere, so the energy bounds below the laminar level
stay undecided; here the laminar state attracts, and that is a theorem — for
every member of the family below a threshold, proved once, restated and
checked for this member, whose balls the decider settles against its compiled
circuit.

## The equations

Writing $a_k$ for the amplitude of $\cos(k \cdot x)$ and $\lambda_k = |k|^2$:

$$ \begin{aligned} a_{10}' &= - \tfrac12 a_{10} - \tfrac{3}{20} a_{11} a_{21} \\ a_{11}' &= 1 - a_{11} + \tfrac{2}{5} a_{10} a_{21} \\ a_{21}' &= - \tfrac52 a_{21} - \tfrac14 a_{10} a_{11} \end{aligned} $$

The laminar state has only the forced mode excited, $a_{11} = f/(2\nu) = 1$,
with energy $E = f^2/(8\nu^2) = \tfrac12$ and enstrophy $Z = f^2/(4\nu^2) = 1$.
Numerically its Jacobian has eigenvalues $-0.48$, $-1$, $-2.52$ — stable — but
nothing below reads that; the theorem is global and needs no linearisation.

**Proved.** From the start where every amplitude is $1$, a solution exists for
all $t \ge 0$ and is unique; its energy stays in $[0, \tfrac{17}{10}]$, its
enstrophy in $[0, 4]$, and its **unforced energy**
$R = a_{10}^2/\lambda_{10} + a_{21}^2/\lambda_{21}$ never exceeds its start value
$\tfrac65$ — all three decided by the trajectory decider from named Lean
contracts. And $R$ decays: $R(t) \le \tfrac65 e^{-t/5}$ for all $t \ge 0$, a
Lean theorem on this page, restated from the member's.

**Refuted.** $R \le 1$ for all $t \ge 0$: false at the start, where
$R = \tfrac65$. The decay says it is true soon after, but the claim is about
every time, and the decider refutes it at $t = 0$.

**Not claimed.** Anything about the Navier–Stokes *equations*; anything about
where $a_{11}$ ends up (the theorem bounds the unforced modes, and the forced
one only through the enstrophy ball); any rate better than $\tfrac15$, which
the crude coupling bound gives, where the linearisation (slowest eigenvalue
$-0.48$, so $R \sim e^{-0.96 t}$) suggests about $1$. "Attracts" here is an
invariant family and a rate, not a status at
a finite time: the deciders state what holds for all $t \ge 0$.

## The system, compiled
-/

namespace Notebook.NSLaminar
open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti Gimle.Forseti.Trajectory

-- @view model Gimle.Forseti.Examples.GalerkinNS.T3S.compiled
-- @evidence simulate Gimle.Forseti.Examples.GalerkinNS.T3S.compiled (h := 1/100) (steps := 3000) (solver := rk4) (plane := a10, a21)

/-!
## What a simulation shows

Drawn as evidence, never a status: the unforced amplitudes $a_{10}$ and
$a_{21}$ fall into the origin of their plane along one direction, without
circling, while $a_{11}$ settles at $1$.
The theorems below say why, and say it for all time.

## Why only the forced mode feeds the rest

Each mode stores $a_k^2/\lambda_k$ and each triad routes energy losslessly, as
in `NS_T3.lean`. Sum the storage identities over the two **unforced** modes
only: the triad's two flows into them do not cancel on their own — they cancel
against the flow into $a_{11}$, which the sum leaves out — so what remains is
exactly the forced mode's own cubic term, with the opposite sign:

$$ R' = -2\nu\,(a_{10}^2 + a_{21}^2) - a_{11} \cdot \tfrac25\, a_{10} a_{21}. $$

That is the whole coupling between the forced mode and the rest, and it is
bounded: $|\tfrac25 a_{10} a_{21}| \le \tfrac15 (a_{10}^2 + a_{21}^2)$, and
$|a_{11}| \le 2$ on the enstrophy ball $Z \le 4$ the start lies in. So
$R' \le -(2\nu - \tfrac25 \cdot 2)\,(a_{10}^2 + a_{21}^2) = -\tfrac15 (a_{10}^2 + a_{21}^2) \le -\tfrac15 R$,
and $R$ decays at rate at least $\tfrac15$. The threshold is
$K r < 2\nu$ with $K = \tfrac25$ the forced mode's coupling sum and $r$ the
enstrophy ball's radius; at $\nu = \tfrac{1}{10}$ the ball must lie above the
laminar enstrophy $f^2/(4\nu^2) = 25$, so $r > 5$ and $K r > 2 > \tfrac15 = 2\nu$;
the generated member takes $r = 6$, where $K r = \tfrac{12}{5}$: above the
threshold, and nothing of this kind is claimed there.
-/

/-- The unforced energy identity for the compiled field. -/
theorem rest_rate (x : Point 3) :
    (∑ i, 2 * (![(1 / 1 : ℝ), 0, (1 / 5 : ℝ)] : Fin 3 → ℝ) i * x i *
        Gimle.Forseti.Nonlinear.field Gimle.Forseti.Examples.GalerkinNS.T3S.compiled x i) =
      -2 * (1 / 2 : ℝ) * (x 0 * x 0 + x 2 * x 2) - x 1 * ((2 / 5 : ℝ) * x 0 * x 2) := by
  rw [Gimle.Forseti.Examples.GalerkinNS.T3S.field_eq]
  simp [Gimle.Forseti.Examples.GalerkinNS.T3S.field, Fin.sum_univ_succ]
  ring

/-- The forced mode's coupling sum, `K = 2/5`. -/
theorem coupling_sum :
    Gimle.Forseti.GalerkinNS.Family.couplingSum Gimle.Forseti.Examples.GalerkinNS.T3S.modes
      Gimle.Forseti.Examples.GalerkinNS.T3S.forcedIndex = 2 / 5 := by
  exact Gimle.Forseti.Examples.GalerkinNS.T3S.couplingSum_eq

/-- Below the threshold: `2ν − K r = 1 − (2/5)·2 = 1/5 > 0`. -/
theorem below_threshold : (0 : ℝ) < 2 * (1 / 2) - 2 / 5 * 2 := by
  norm_num

/-- The same modes at `ν = 1/10` are above it: any ball above the laminar
enstrophy `25` has `r > 5`; with the member's `r = 6`, `2ν − K r = 1/5 − 12/5 < 0`. -/
theorem above_threshold_at_small_viscosity : (2 * (1 / 10 : ℝ) - 2 / 5 * 6) < 0 := by
  norm_num

/-- **The unforced energy decays**: along every realization of the compiled
model, `R(t) ≤ R(0) e^{−t/5}`, with `R(0) = 6/5`. -/
theorem rest_decays (state : Signal 3)
    (realized : Gimle.Forseti.Examples.GalerkinNS.T3S.compiled.Realizes state) :
    ∀ t ∈ Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.time.domain,
      Gimle.Forseti.Examples.GalerkinNS.T3S.rest (state t) ≤
        6 / 5 * Real.exp (-(1 / 5 : ℝ) * t) := by
  intro t ht
  have h := Gimle.Forseti.Examples.GalerkinNS.T3S.rest_decays state realized t ht
  rw [Gimle.Forseti.Examples.GalerkinNS.T3S.couplingSum_eq] at h
  have start : Gimle.Forseti.Examples.GalerkinNS.T3S.rest
      Gimle.Forseti.Examples.GalerkinNS.T3S.compiled.initial = 6 / 5 := by
    rw [Gimle.Forseti.Examples.GalerkinNS.T3S.initial_eq]
    simp [Gimle.Forseti.Examples.GalerkinNS.T3S.rest, Matrix.cons_val]
    norm_num
  have zero : Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.time.start = 0 := by
    simp [Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.T3S.evolution]
  rw [start, zero] at h
  convert h using 2
  norm_num

/-!
## For every member

The theorem is the family's: for any nonzero modes containing $(1,1)$, any
$\nu > 0$ and any $r \ge 0$ with $r^2$ above the laminar enstrophy
$f^2/(4\nu^2)$ and $K r < 2\nu$, from any start with $Z \le r^2$ a solution
exists for all $t \ge$ the start, is unique, keeps $Z \le r^2$ and has
$R(t) \le R(\text{start})\, e^{-(2\nu - K r)(t - \text{start})}$. The member
above is an instance.
-/

/-- **Every member below the threshold.** -/
theorem every_member {n : ℕ} (k : Fin n → Gimle.Forseti.GalerkinNS.Family.Wave)
    (hk : ∀ i, k i ≠ 0) (forced : Fin n) (hf : k forced = (1, 1)) (ν f r : ℝ) (hν : 0 < ν)
    (hr : 0 ≤ r) (hC : f ^ 2 / (4 * ν ^ 2) < r ^ 2)
    (hγ : 0 < 2 * ν - Gimle.Forseti.GalerkinNS.Family.couplingSum k forced * r)
    (time : TimeDomain) (x₀ : Point n) (initial : Gimle.Forseti.GalerkinNS.Family.enstrophy x₀ ≤ r ^ 2) :
    ∀ state, Gimle.Forseti.Nonlinear.Solves (Gimle.Forseti.GalerkinNS.Family.field ν f k forced) time x₀ state →
      ∀ t ∈ time.domain,
        Gimle.Forseti.GalerkinNS.Family.restEnergy k forced (state t) ≤
          Gimle.Forseti.GalerkinNS.Family.restEnergy k forced x₀ *
            Real.exp (-(2 * ν - Gimle.Forseti.GalerkinNS.Family.couplingSum k forced * r) * (t - time.start)) := by
  intro state h t ht
  exact ((Gimle.Forseti.GalerkinNS.Family.laminar_attracts ν f hν k hk forced hf r hr hC hγ
    time x₀ initial).2.2 state h t ht).2

/-!
## The claims, decided

Every claim below is decided against the compiled circuit from a one-line
goal: the enstrophy ball the decay is proved on, the energy ball at the start
level, the unforced energy never above its start, and a bound below the start
refuted at the start.
-/

-- @decide in_enstrophy_ball : trajectory ns-t3s from (1, 1, 1) at 0 observe Z always : Z >= 0 and Z <= 4

namespace DecidedShared_9a6160343b19

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 3 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 6 := ⟨4, by decide⟩

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.states.map (·.initialId) = ["initial-a10", "initial-a11", "initial-a21"] ∧
  (Gimle.Forseti.Examples.GalerkinNS.T3S.body.observations.get forsetiObservation).port.id =
    "obs-z" ∧
  Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.axis.id = "time"

end DecidedShared_9a6160343b19

namespace Decided_in_enstrophy_ball

open DecidedShared_9a6160343b19

example : @forsetiTime = @DecidedShared_9a6160343b19.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_9a6160343b19.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_9a6160343b19.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_9a6160343b19.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (4) 1))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["Z"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (4) 1)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.T3S.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- Z is output 4 of the compiled circuit, the port obs-z; the input's initial wires (initial-a10, initial-a11, initial-a21) start at (1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-t3s interpretation continuous-real obligation contract start time = 0 initial initial-a10 = 1, initial-a11 = 1, initial-a21 = 1 observe obs-z as Z always : Z >= 0 and Z <= 4 -/
theorem in_enstrophy_ball :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.T3S.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y →
        ∀ t ≥ 0, have Z := y t 4; Z ≥ 0 ∧ Z ≤ 4) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.T3S.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.T3S.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.T3S.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.T3S.enstrophyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.T3S.enstrophy_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (4) 1) : ℚ) : ℝ) = 4 := by norm_num [Rat.mkRat_eq_div]
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


-- @decide in_energy_ball : trajectory ns-t3s from (1, 1, 1) at 0 observe E always : E >= 0 and E <= 17/10

namespace DecidedShared_f551903755fb

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 3 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 6 := ⟨3, by decide⟩

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.states.map (·.initialId) = ["initial-a10", "initial-a11", "initial-a21"] ∧
  (Gimle.Forseti.Examples.GalerkinNS.T3S.body.observations.get forsetiObservation).port.id =
    "obs-e" ∧
  Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.axis.id = "time"

end DecidedShared_f551903755fb

namespace Decided_in_energy_ball

open DecidedShared_f551903755fb

example : @forsetiTime = @DecidedShared_f551903755fb.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_f551903755fb.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_f551903755fb.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_f551903755fb.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (17) 10))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["E"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (17) 10)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.T3S.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- E is output 3 of the compiled circuit, the port obs-e; the input's initial wires (initial-a10, initial-a11, initial-a21) start at (1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-t3s interpretation continuous-real obligation contract start time = 0 initial initial-a10 = 1, initial-a11 = 1, initial-a21 = 1 observe obs-e as E always : E >= 0 and E <= 17/10 -/
theorem in_energy_ball :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.T3S.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y →
        ∀ t ≥ 0, have E := y t 3; E ≥ 0 ∧ E ≤ 17/10) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.T3S.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.T3S.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.T3S.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.T3S.energyIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.T3S.energy_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (17) 10) : ℚ) : ℝ) = (17/10) := by norm_num [Rat.mkRat_eq_div]
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

end Decided_in_energy_ball


-- @decide rest_never_grows : trajectory ns-t3s from (1, 1, 1) at 0 observe R always : R >= 0 and R <= 6/5

namespace DecidedShared_e85b1539f483

def forsetiTime : Gimle.Asgard.Dynamics.TimeDomain :=
  ⟨"time", (((mkRat (0) 1) : ℚ) : ℝ)⟩

def forsetiInitial : Gimle.Asgard.Point 3 :=
  ![(((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ), (((mkRat (1) 1) : ℚ) : ℝ)]

def forsetiObservation : Fin 6 := ⟨5, by decide⟩

def forsetiIdentities : Prop :=
  Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.states.map (·.initialId) = ["initial-a10", "initial-a11", "initial-a21"] ∧
  (Gimle.Forseti.Examples.GalerkinNS.T3S.body.observations.get forsetiObservation).port.id =
    "obs-r" ∧
  Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.axis.id = "time"

end DecidedShared_e85b1539f483

namespace Decided_rest_never_grows

open DecidedShared_e85b1539f483

example : @forsetiTime = @DecidedShared_e85b1539f483.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_e85b1539f483.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_e85b1539f483.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_e85b1539f483.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.and (.atom .ge (.var ⟨0, by decide⟩)) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (6) 5))))))

def forsetiLeaf : Gimle.Forseti.Syntax.Goal :=
  ⟨⟨["R"], by decide, by decide, by decide⟩,
    (.and (.atom .le (.neg (.var ⟨0, by decide⟩))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (6) 5)))))),
    forsetiPost⟩

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.T3S.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- R is output 5 of the compiled circuit, the port obs-r; the input's initial wires (initial-a10, initial-a11, initial-a21) start at (1, 1, 1) at time = 0. The trajectory decider proved it. Goal (trajectory): trajectory ns-t3s interpretation continuous-real obligation contract start time = 0 initial initial-a10 = 1, initial-a11 = 1, initial-a21 = 1 observe obs-r as R always : R >= 0 and R <= 6/5 -/
theorem rest_never_grows :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.T3S.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y →
        ∀ t ≥ 0, have R := y t 5; R ≥ 0 ∧ R ≤ 6/5) := by
  have root : forsetiRoot := by
    unfold forsetiRoot forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.T3S.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.T3S.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.T3S.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.T3S.restIndex := rfl
    rw [time, init, obs]
    refine Gimle.Forseti.Trajectory.Contract.consequence Gimle.Forseti.Examples.GalerkinNS.T3S.rest_contract (fun _ admitted => admitted) ?_
    intro o band t within
    have leaf := Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiLeaf ⟨[⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[]⟩, ⟨[((mkRat (1) 1), (.constant (mkRat (1) 1)))]⟩]⟩]⟩ (by decide +kernel)
    apply leaf
    simp only [forsetiLeaf, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval]
    obtain ⟨low, high⟩ := band t within
    refine ⟨?_, ?_⟩ <;> norm_num [Rat.mkRat_eq_div] <;> linarith
  have forsetiCast0 : (((mkRat (6) 5) : ℚ) : ℝ) = (6/5) := by norm_num [Rat.mkRat_eq_div]
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

end Decided_rest_never_grows


-- @decide rest_below_one : trajectory ns-t3s from (1, 1, 1) at 0 observe R always : R <= 1

namespace Decided_rest_below_one

open DecidedShared_e85b1539f483

example : @forsetiTime = @DecidedShared_e85b1539f483.forsetiTime := rfl
example : @forsetiInitial = @DecidedShared_e85b1539f483.forsetiInitial := rfl
example : @forsetiObservation = @DecidedShared_e85b1539f483.forsetiObservation := rfl
example : @forsetiIdentities = @DecidedShared_e85b1539f483.forsetiIdentities := rfl

def forsetiPost : Gimle.Forseti.Syntax.Formula 1 :=
  (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1)))))

def forsetiContract : Prop :=
  Gimle.Forseti.Trajectory.Contract Gimle.Forseti.Examples.GalerkinNS.T3S.observed forsetiTime
    (Gimle.Forseti.Trajectory.Initialized forsetiTime (fun _ => True)
      (· = forsetiInitial))
    (Gimle.Forseti.Trajectory.Always forsetiTime
      fun o => forsetiPost.holds (fun _ => o forsetiObservation))

def forsetiRoot : Prop := forsetiIdentities ∧ forsetiContract

/-- R is output 5 of the compiled circuit, the port obs-r; the input's initial wires (initial-a10, initial-a11, initial-a21) start at (1, 1, 1) at time = 0. The trajectory decider refuted it. Goal (trajectory): trajectory ns-t3s interpretation continuous-real obligation contract start time = 0 initial initial-a10 = 1, initial-a11 = 1, initial-a21 = 1 observe obs-r as R always : R <= 1 -/
theorem rest_below_one :
    have circuit := Gimle.Forseti.Examples.GalerkinNS.T3S.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y →
        ∀ t ≥ 0, have R := y t 5; R ≤ 1) := by
  sorry

theorem rest_below_one_refuted : ¬ (have circuit := Gimle.Forseti.Examples.GalerkinNS.T3S.observed
    have time : Gimle.Asgard.Dynamics.TimeDomain := ⟨"time", 0⟩
    ∀ u : Gimle.Asgard.Dynamics.Signal (0 + 3),
      Gimle.Asgard.Dynamics.signalRight u 0 = ![1, 1, 1] →
      (∃ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y) ∧
      (∀ y y' : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y → circuit.Rel time u y' →
        ∀ t ≥ 0, y t = y' t) ∧
      (∀ y : Gimle.Asgard.Dynamics.Signal 6, circuit.Rel time u y →
        ∀ t ≥ 0, have R := y t 5; R ≤ 1)) := by
  have refuted : forsetiIdentities ∧ ¬ forsetiContract := by
    unfold forsetiIdentities forsetiContract
    refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
    intro contract
    have time : forsetiTime = Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.time := by simp [forsetiTime, Gimle.Asgard.Model.Evolution.time, Gimle.Forseti.Examples.GalerkinNS.T3S.evolution] <;> norm_num [Rat.mkRat_eq_div]
    have init : forsetiInitial = Gimle.Forseti.Examples.GalerkinNS.T3S.compiled.initial := by rw [Gimle.Forseti.Examples.GalerkinNS.T3S.initial_eq]; funext i; fin_cases i <;> norm_num [forsetiInitial, Rat.mkRat_eq_div]
    have obs : forsetiObservation = Gimle.Forseti.Examples.GalerkinNS.T3S.restIndex := rfl
    rw [time, init, obs] at contract
    obtain ⟨state, realized⟩ := Gimle.Forseti.Examples.GalerkinNS.T3S.compiled_exists
    have start : state Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.time.start = Gimle.Forseti.Examples.GalerkinNS.T3S.compiled.initial := by unfold Gimle.Asgard.Model.ContinuousModel.Realizes Gimle.Asgard.Model.ContinuousModel.feedback at realized; exact ((Gimle.Forseti.Trajectory.close_rel _ _ _ _ _ _).mp realized).2.1
    have bounded := contract.holds _ Gimle.Forseti.Examples.GalerkinNS.T3S.declared_input_admitted _ ⟨state, (Gimle.Forseti.Examples.GalerkinNS.T3S.feedback_reads _ Gimle.Forseti.Examples.GalerkinNS.T3S.declared_input_admitted state).mpr realized, rfl⟩ Gimle.Forseti.Examples.GalerkinNS.T3S.evolution.time.start (by simp [Gimle.Asgard.Dynamics.TimeDomain.domain])
    simp only at bounded
    rw [start, Gimle.Forseti.Examples.GalerkinNS.T3S.rest_at_initial] at bounded
    have witness : forsetiPost.holds (fun i => (((fun _ : Fin 1 => (mkRat (6) 5)) i : ℚ) : ℝ)) := by convert bounded using 2; norm_num [Rat.mkRat_eq_div]
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

end Decided_rest_below_one


#print axioms rest_rate
#print axioms coupling_sum
#print axioms below_threshold
#print axioms above_threshold_at_small_viscosity
#print axioms rest_decays
#print axioms every_member

end Notebook.NSLaminar
