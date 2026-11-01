import AIFSafety.TrajectoryContract

/-! Hostile and boundary regressions for the typed AIF input contract. -/
namespace AIFSafety.TrajectoryContractRegressions
open Gimle.Forseti Gimle.Forseti.Examples
open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory
open TrajectoryContract

theorem changed_initial_rejected (eta : ℝ) : ¬ admitted eta
    (signalAppend (Gimle.Asgard.Examples.AIF.drivers eta)
      (fun _ => (![1,0,0,0] : Point 4))) := by
  intro h
  have wrong := congrFun h.2 0
  norm_num [signalRight_append] at wrong

theorem varying_eta_rejected (eta : ℝ) : ¬ admitted eta
    (signalAppend (fun t => (![eta+t] : Point 1)) (fun _ => (0 : Point 4))) := by
  intro h
  have wrong := congrFun (congrFun h.1 1) 0
  norm_num [signalLeft_append, Gimle.Asgard.Examples.AIF.drivers] at wrong

theorem initial_wires_read_only_at_start (eta : ℝ) : admitted eta
    (signalAppend (Gimle.Asgard.Examples.AIF.drivers eta)
      (fun t => (![t,t,t,t] : Point 4))) := by
  constructor
  · simp [signalLeft_append]
  · ext i
    fin_cases i <;> simp [signalRight_append, Gimle.Asgard.Examples.AIF.time]

theorem lower_endpoint_contract :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted 8)
      (fun output => ∀ t ∈ Set.Icc (0 : ℝ) (21/200),
        0 ≤ output t 0 ∧ output t 0 ≤ 16/5) :=
  startup_contract 8 (by norm_num)

theorem upper_endpoint_contract :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted 12)
      (fun output => ∀ t ∈ Set.Icc (0 : ℝ) (21/200),
        0 ≤ output t 0 ∧ output t 0 ≤ 16/5) :=
  startup_contract 12 (by norm_num)

/-- The admitted-input predicate has a witness with an actual safe observed behavior. -/
theorem safe_behavior_exists (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    ∃ output, observed.Rel Gimle.Asgard.Examples.AIF.time
      (signalAppend (Gimle.Asgard.Examples.AIF.drivers eta) (fun _ => (0 : Point 4))) output ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (21/200), 0 ≤ output t 0 ∧ output t 0 ≤ 16/5 :=
  (startup_contract eta hp).exists_safe _ (declared_input_admitted eta)

#print axioms changed_initial_rejected
#print axioms varying_eta_rejected
#print axioms initial_wires_read_only_at_start
#print axioms lower_endpoint_contract
#print axioms upper_endpoint_contract
#print axioms safe_behavior_exists
end AIFSafety.TrajectoryContractRegressions
