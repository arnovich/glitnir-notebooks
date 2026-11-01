import AIFSafety.UniformPrefix
import Gimle.Forseti.Trajectory

/-! Typed contracts for the original compiled feedback followed by its output.
Startup safety is discharged here. The larger-horizon contracts take both
all-cell certificate families as arguments; `CompleteSafety` supplies them. -/
namespace AIFSafety.TrajectoryContract
open Gimle.Forseti Gimle.Forseti.Examples
open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory

/-- The original compiled feedback followed by the original x2 observer. -/
def observed : Dynamics.Circuit 5 1 :=
  .compose Gimle.Asgard.Examples.AIF.feedback (.lift Gimle.Asgard.Examples.AIF.output)

/-- Eta is fixed as a driver; only the initial-wire value at time zero is read. -/
def admitted (eta : ℝ) : SignalPredicate 5 :=
  Initialized Gimle.Asgard.Examples.AIF.time
    (fun driver => driver = Gimle.Asgard.Examples.AIF.drivers eta)
    (fun initial => initial = (0 : Point 4))

theorem feedback_reads (eta : ℝ) (input : Signal 5) (hi : admitted eta input)
    (state : Signal 4) :
    Gimle.Asgard.Examples.AIF.feedback.Rel Gimle.Asgard.Examples.AIF.time input state ↔
      Gimle.Asgard.Examples.AIF.Realizes eta state := by
  rw [Gimle.Asgard.Examples.AIF.feedback, close_rel_reads_start, hi.1, hi.2]
  rfl

theorem declared_input_admitted (eta : ℝ) : admitted eta
    (signalAppend (Gimle.Asgard.Examples.AIF.drivers eta) (fun _ => (0 : Point 4))) := by
  constructor <;> simp [signalLeft_append, signalRight_append]

theorem observed_rel (input : Signal 5) (output : Signal 1) :
    observed.Rel Gimle.Asgard.Examples.AIF.time input output ↔
      ∃ state, Gimle.Asgard.Examples.AIF.feedback.Rel
        Gimle.Asgard.Examples.AIF.time input state ∧
        output = fun t => Gimle.Asgard.Examples.AIF.output.run (state t) := Iff.rfl

/-- Lift a bound on every realization into the existing total typed contract. -/
theorem contract_of_realizations (eta : ℝ) (heta : 0 ≤ eta)
    (post : SignalPredicate 1)
    (safe : ∀ state, Gimle.Asgard.Examples.AIF.Realizes eta state →
      post (fun t => Gimle.Asgard.Examples.AIF.output.run (state t))) :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted eta) post where
  realizable input hi := by
    obtain ⟨state, realized⟩ := AIFCircuitBinding.exists_realization eta heta
    refine ⟨fun t => Gimle.Asgard.Examples.AIF.output.run (state t), ?_⟩
    exact (observed_rel input _).mpr ⟨state, (feedback_reads eta input hi state).mpr realized, rfl⟩
  unique input hi first second hfirst hsecond := by
    obtain ⟨x, hx, rfl⟩ := (observed_rel input first).mp hfirst
    obtain ⟨y, hy, rfl⟩ := (observed_rel input second).mp hsecond
    have same := AIFCircuitBinding.realization_unique eta heta x y
      ((feedback_reads eta input hi x).mp hx) ((feedback_reads eta input hi y).mp hy)
    intro t ht
    exact congrArg Gimle.Asgard.Examples.AIF.output.run (same ht)
  holds input hi output related := by
    obtain ⟨state, hs, rfl⟩ := (observed_rel input output).mp related
    exact safe state ((feedback_reads eta input hi state).mp hs)

/-- No missing-certificate or trajectory assumptions remain on this prefix. -/
theorem startup_contract (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted eta)
      (fun output => ∀ t ∈ Set.Icc (0 : ℝ) (21/200),
        0 ≤ output t 0 ∧ output t 0 ≤ 16/5) := by
  apply contract_of_realizations eta (by linarith [hp.1])
  exact (UniformPrefix.all_parameter_safety eta hp).2

/-- The all-forward contract, given both all-cell certificate families. -/
theorem forward_contract (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (drift : ∀ b i, StartupPrefix.CellDrift b i)
    (output : ∀ b i, SafetyComposition.CellOutput b i) :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted eta)
      (Always Gimle.Asgard.Examples.AIF.time fun y => 0 ≤ y 0 ∧ y 0 ≤ 16/5) := by
  apply contract_of_realizations eta (by linarith [hp.1])
  exact (SafetyComposition.forward_safety_of_certificates drift output eta hp).2

/-- The time-100 contract, given both all-cell certificate families. -/
theorem hundred_contract (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (drift : ∀ b i, StartupPrefix.CellDrift b i)
    (output : ∀ b i, SafetyComposition.CellOutput b i) :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted eta)
      (fun y => ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 ≤ y t 0 ∧ y t 0 ≤ 16/5) := by
  apply (forward_contract eta hp drift output).consequence (fun _ h => h)
  intro y hy t ht
  exact hy t ht.1

#print axioms feedback_reads
#print axioms declared_input_admitted
#print axioms observed_rel
#print axioms contract_of_realizations
#print axioms startup_contract
#print axioms forward_contract
#print axioms hundred_contract
end AIFSafety.TrajectoryContract
