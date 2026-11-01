import AIFSafety.CompleteFamily
import AIFSafety.TrajectoryContract

/-! Safety of antithetic integral feedback. For every fixed `eta ∈ [8, 12]`, the
compiled circuit started at zero has exactly one behaviour, its species stay
nonnegative, and its output `x₂` stays in `[0, 16/5]` for all `t ≥ 0` and below
`5/2` from `t = 30` on. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteSafety
open Gimle.Forseti Gimle.Forseti.Examples

open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory

theorem forward_safety (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    (∃ state : Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    ∀ state : Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Ici (0 : ℝ),
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 :=
  SafetyComposition.forward_safety_of_certificates
    CompleteFamily.drift CompleteFamily.output eta hp

theorem hundred_safety (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    (∃ state : Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    ∀ state : Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Icc (0 : ℝ) 100,
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  refine ⟨(forward_safety eta hp).1, ?_⟩
  intro state realized t ht
  exact (forward_safety eta hp).2 state realized t ht.1

theorem forward_contract (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    Contract TrajectoryContract.observed Gimle.Asgard.Examples.AIF.time
      (TrajectoryContract.admitted eta)
      (Always Gimle.Asgard.Examples.AIF.time fun y => 0 ≤ y 0 ∧ y 0 ≤ 16/5) :=
  TrajectoryContract.forward_contract eta hp CompleteFamily.drift CompleteFamily.output

theorem hundred_contract (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    Contract TrajectoryContract.observed Gimle.Asgard.Examples.AIF.time
      (TrajectoryContract.admitted eta)
      (fun y => ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 ≤ y t 0 ∧ y t 0 ≤ 16/5) :=
  TrajectoryContract.hundred_contract eta hp CompleteFamily.drift CompleteFamily.output

theorem later_output (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Signal 4) (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : 30 ≤ t) : Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 5/2 :=
  SafetyComposition.later_output CompleteFamily.drift eta hp state realized t ht

theorem species_nonnegative (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Signal 4) (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 4) : 0 ≤ state t i :=
  AIFCircuitBinding.realization_nonnegative eta (by linarith [hp.1]) state realized t ht i

theorem realization_unique (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (x y : Signal 4) (hx : Gimle.Asgard.Examples.AIF.Realizes eta x)
    (hy : Gimle.Asgard.Examples.AIF.Realizes eta y) : Set.EqOn x y (Set.Ici 0) :=
  AIFCircuitBinding.realization_unique eta (by linarith [hp.1]) x y hx hy

theorem safe_behavior_exists (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    ∃ output, TrajectoryContract.observed.Rel Gimle.Asgard.Examples.AIF.time
      (signalAppend (Gimle.Asgard.Examples.AIF.drivers eta) (fun _ => (0 : Point 4))) output ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 ≤ output t 0 ∧ output t 0 ≤ 16/5 :=
  (hundred_contract eta hp).exists_safe _ (TrajectoryContract.declared_input_admitted eta)

/-- `forward_safety` with its quantifiers inside, stated word for word as the
AntitheticFeedback notebook's `ForwardSafety`. -/
theorem forward_safety_statement :
  ∀ eta ∈ Set.Icc (8 : ℝ) 12,
    (∃ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    ∀ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Ici (0 : ℝ),
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 :=
  forward_safety

/-- `later_output`, stated word for word as the notebook's `LaterOutput`. -/
theorem later_output_statement :
  ∀ eta ∈ Set.Icc (8 : ℝ) 12, ∀ state : Dynamics.Signal 4,
    Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t, 30 ≤ t → Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 5/2 :=
  later_output

#print axioms forward_safety
#print axioms hundred_safety
#print axioms forward_contract
#print axioms hundred_contract
#print axioms later_output
#print axioms species_nonnegative
#print axioms realization_unique
#print axioms safe_behavior_exists
#print axioms forward_safety_statement
#print axioms later_output_statement
end AIFSafety.CompleteSafety
