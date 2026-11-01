import AIFSafety.CompleteSafety
import AIFSafety.TrajectoryContractRegressions

/-! Inputs the safety theorems must reject: a changed initial state, a
time-varying `eta`, and a start at the equilibrium. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteSafetyRegressions
open Gimle.Forseti Gimle.Forseti.Examples

open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory
open TrajectoryContract

theorem changed_initial_rejected (eta : ℝ) : ¬ admitted eta
    (signalAppend (Gimle.Asgard.Examples.AIF.drivers eta) (fun _ => (![1,0,0,0] : Point 4))) :=
  TrajectoryContractRegressions.changed_initial_rejected eta

theorem varying_eta_rejected (eta : ℝ) : ¬ admitted eta
    (signalAppend (fun t => (![eta+t] : Point 1)) (fun _ => (0 : Point 4))) :=
  TrajectoryContractRegressions.varying_eta_rejected eta

theorem initial_wires_read_only_at_start (eta : ℝ) : admitted eta
    (signalAppend (Gimle.Asgard.Examples.AIF.drivers eta) (fun t => (![t,t,t,t] : Point 4))) :=
  TrajectoryContractRegressions.initial_wires_read_only_at_start eta

theorem lower_endpoint_contract :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted 8)
      (fun output => ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 ≤ output t 0 ∧ output t 0 ≤ 16/5) :=
  CompleteSafety.hundred_contract 8 (by norm_num)

theorem upper_endpoint_contract :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted 12)
      (fun output => ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 ≤ output t 0 ∧ output t 0 ≤ 16/5) :=
  CompleteSafety.hundred_contract 12 (by norm_num)

theorem time_zero_bound (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Signal 4) (realized : Gimle.Asgard.Examples.AIF.Realizes eta state) :
    0 ≤ Gimle.Asgard.Examples.AIF.output.run (state 0) 0 ∧
    Gimle.Asgard.Examples.AIF.output.run (state 0) 0 ≤ 16/5 :=
  (CompleteSafety.hundred_safety eta hp).2 state realized 0 (by norm_num)

theorem time_hundred_bound (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Signal 4) (realized : Gimle.Asgard.Examples.AIF.Realizes eta state) :
    0 ≤ Gimle.Asgard.Examples.AIF.output.run (state 100) 0 ∧
    Gimle.Asgard.Examples.AIF.output.run (state 100) 0 ≤ 16/5 :=
  (CompleteSafety.hundred_safety eta hp).2 state realized 100 (by norm_num)

theorem terminal_bound (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Signal 4) (realized : Gimle.Asgard.Examples.AIF.Realizes eta state) :
    Gimle.Asgard.Examples.AIF.output.run (state 30) 0 ≤ 5/2 :=
  CompleteSafety.later_output eta hp state realized 30 (by norm_num)

/-- `Realizes` itself pins the zero start: the equilibrium is not a behaviour. -/
theorem equilibrium_start_rejected (eta : ℝ) :
    ¬ Gimle.Asgard.Examples.AIF.Realizes eta (fun _ => ![2, 2, 2, 1/eta]) := by
  intro realized
  have start := congrFun ((Gimle.Asgard.Examples.AIF.realizes_iff eta _).1 realized).1 0
  norm_num at start

#print axioms changed_initial_rejected
#print axioms varying_eta_rejected
#print axioms initial_wires_read_only_at_start
#print axioms lower_endpoint_contract
#print axioms upper_endpoint_contract
#print axioms time_zero_bound
#print axioms time_hundred_bound
#print axioms terminal_bound
#print axioms equilibrium_start_rejected
end AIFSafety.CompleteSafetyRegressions
