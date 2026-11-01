import Gimle.Forseti.Examples.AIFCircuitBinding
import AIFSafety.StartupOutput

/-! Existence, forward uniqueness and nonnegativity of the actual compiled AIF
feedback, with output safety on the already certified startup prefixes. -/
namespace AIFSafety.CircuitSolution
open Gimle.Forseti Gimle.Forseti.Examples
open Gimle.Asgard

/-- Nonempty original feedback behavior and universal output safety on the checked
all-parameter startup interval. -/
theorem startup_safety (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    (∃ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    (∀ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Icc (0 : ℝ) (1/200),
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5) := by
  have heta : 0 ≤ eta := by linarith [hp.1]
  refine ⟨AIFCircuitBinding.exists_realization eta heta, ?_⟩
  intro state realized t ht
  exact ⟨AIFCircuitBinding.realization_output_nonnegative eta heta state realized t ht.1,
    StartupOutput.all_parameter_output eta hp state realized t ht⟩

/-- The same nonempty universal safety statement for the longer checked bin-zero prefix. -/
theorem bin0_safety (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) (17/2)) :
    (∃ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    (∀ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Icc (0 : ℝ) (21/200),
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5) := by
  have heta : 0 ≤ eta := by linarith [hp.1]
  refine ⟨AIFCircuitBinding.exists_realization eta heta, ?_⟩
  intro state realized t ht
  exact ⟨AIFCircuitBinding.realization_output_nonnegative eta heta state realized t ht.1,
    StartupOutput.bin0_prefix_output eta hp state realized t ht⟩

#print axioms startup_safety
#print axioms bin0_safety
end AIFSafety.CircuitSolution
