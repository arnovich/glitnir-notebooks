import AIFSafety.CircuitSolution
import AIFSafety.TerminalEntryBin0
import AIFSafety.TerminalEntryBin1
import AIFSafety.TerminalEntryBin2
import AIFSafety.TerminalEntryBin3
import AIFSafety.TerminalEntryBin4
import AIFSafety.TerminalEntryBin5
import AIFSafety.TerminalEntryBin6
import AIFSafety.TerminalEntryBin7

/-! End-to-end safety, parameterised by the all-cell drift and output families.
`CompleteSafety` supplies them from `CompleteFamily`. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.SafetyComposition
open Gimle.Forseti Gimle.Forseti.Examples
open AIFMesh AIFSlabModel AIFPhysicalCoordinates AIFLocalEntry

/-- Output enclosure obligation for one exact candidate cell. -/
def CellOutput (b : Fin 8) (i : Fin 370) : Prop :=
  ∀ t eta (x : Fin 4 → ℝ),
    t ∈ Set.Icc ((CandidateMesh.mesh.slab b i).tStart : ℝ)
      (((CandidateMesh.mesh.slab b i).tStart : ℝ)+(CandidateMesh.mesh.slab b i).step) →
    eta ∈ Set.Icc ((CandidateMesh.mesh.slab b i).etaLo : ℝ)
      ((CandidateMesh.mesh.slab b i).etaHi : ℝ) →
    tubeEnergy (CandidateMesh.mesh.slab b i) t eta x ≤ 1/40000 → x 1 ≤ 6/5

theorem full_prefix : StartupPrefix.prefixMesh 370 (by decide)=CandidateMesh.mesh := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem terminal_time : CandidateMesh.mesh.times 370=30 := by decide +kernel

/-- The eight independently checked terminal certificates cover every bin. -/
theorem terminal_entry (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc ((CandidateMesh.mesh.slab b 369).etaLo : ℝ)
      ((CandidateMesh.mesh.slab b 369).etaHi : ℝ))
    (x : Fin 4 → ℝ)
    (tube : tubeEnergy (CandidateMesh.mesh.slab b 369) 30 eta x ≤ 1/40000) :
    value x ≤ 3/400 ∧ value x < 1/100 := by
  fin_cases b
  · exact TerminalEntryBin0.entry_at_thirty eta hp x tube
  · exact TerminalEntryBin1.entry_at_thirty eta hp x tube
  · exact TerminalEntryBin2.entry_at_thirty eta hp x tube
  · exact TerminalEntryBin3.entry_at_thirty eta hp x tube
  · exact TerminalEntryBin4.entry_at_thirty eta hp x tube
  · exact TerminalEntryBin5.entry_at_thirty eta hp x tube
  · exact TerminalEntryBin6.entry_at_thirty eta hp x tube
  · exact TerminalEntryBin7.entry_at_thirty eta hp x tube

/-- Every startup cell needs a checked drift result before full propagation applies. -/
theorem startup_membership
    (drift : ∀ b i, StartupPrefix.CellDrift b i)
    (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (CandidateMesh.mesh.edges b.castSucc : ℝ)
      (CandidateMesh.mesh.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state) :
    ∀ i, ∀ t ∈ Set.Icc (CandidateMesh.mesh.times i.castSucc : ℝ)
      (CandidateMesh.mesh.times i.succ : ℝ),
      tubeEnergy (CandidateMesh.mesh.slab b i) t eta (shift eta (state t)) ≤ 1/40000 := by
  have h := StartupPrefix.prefix_invariant 369 (by decide) b eta hp state realized
    (fun i => drift b i)
  simpa only [full_prefix] using! h

/-- Complete startup drift certification supplies the terminal membership premise. -/
theorem local_entry_of_startup
    (drift : ∀ b i, StartupPrefix.CellDrift b i)
    (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (CandidateMesh.mesh.edges b.castSucc : ℝ)
      (CandidateMesh.mesh.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state) :
    value (shift eta (state 30)) < 1/100 := by
  apply (terminal_entry b eta hp (shift eta (state 30)) _).2
  apply startup_membership drift b eta hp state realized 369 30
  have hq := MeshGeometry.time_positive 369
  change CandidateMesh.mesh.times 369 < CandidateMesh.mesh.times 370 at hq
  rw [terminal_time] at hq
  change (CandidateMesh.mesh.times 369 : ℝ) ≤ 30 ∧ 30 ≤ (CandidateMesh.mesh.times 370 : ℝ)
  constructor
  · exact_mod_cast (le_of_lt hq)
  · rw [terminal_time]
    norm_num

/-- Actual compiled output stays below 5/2 after certified local entry. -/
theorem output_after_entry (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (entry : value (shift eta (state 30)) ≤ 1/100)
    (t : ℝ) (ht : 30 ≤ t) : Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 5/2 := by
  have physical := (AIFCircuitBinding.realizes_iff_physical eta state).mp realized
  have hsubset : Set.Icc (30 : ℝ) t ⊆ Set.Ici 0 := by
    intro z hz
    change 0 ≤ z
    linarith [hz.1]
  have h := AIFLocalStability.physical_output_bound eta hp state 30 t
    (fun s hs i => (physical.2 s (hsubset hs) i).mono hsubset) entry t ⟨ht,le_rfl⟩
  rw [Gimle.Asgard.Examples.AIF.output_correct]
  exact h

/-- Sharp startup output requires both complete drift and output certificate families. -/
theorem startup_output
    (drift : ∀ b i, StartupPrefix.CellDrift b i)
    (output : ∀ b i, CellOutput b i)
    (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 30) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  obtain ⟨b,i,hti,hpi⟩ := CandidateMesh.covers t eta ht hp
  apply (AIFCircuitBinding.compiled_output_bound_iff eta (state t)).mpr
  apply output b i t eta (shift eta (state t)) hti hpi
  apply startup_membership drift b eta hpi state realized i t
  simpa only [Mesh.slab,Rat.cast_sub,add_sub_cancel] using hti

/-- After startup, all future times are covered by the local invariant region. -/
theorem later_output
    (drift : ∀ b i, StartupPrefix.CellDrift b i)
    (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : 30 ≤ t) : Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 5/2 := by
  obtain ⟨b,_,_,hb⟩ := CandidateMesh.covers 30 eta (by norm_num) hp
  exact output_after_entry eta hp state realized
    (le_of_lt (local_entry_of_startup drift b eta hb state realized)) t ht

/-- Nonempty forward behavior and universal nonnegative output safety, given every
cell's drift and output certificate. -/
theorem forward_safety_of_certificates
    (drift : ∀ b i, StartupPrefix.CellDrift b i)
    (output : ∀ b i, CellOutput b i)
    (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    (∃ state : Gimle.Asgard.Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    (∀ state : Gimle.Asgard.Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Ici (0 : ℝ),
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5) := by
  have heta : 0 ≤ eta := by linarith [hp.1]
  refine ⟨AIFCircuitBinding.exists_realization eta heta, ?_⟩
  intro state realized t ht
  refine ⟨AIFCircuitBinding.realization_output_nonnegative eta heta state realized t ht, ?_⟩
  rcases le_total t 30 with h | h
  · exact startup_output drift output eta hp state realized t ⟨ht,h⟩
  · have hlate := later_output drift eta hp state realized t h
    linarith

#print axioms full_prefix
#print axioms terminal_time
#print axioms terminal_entry
#print axioms startup_membership
#print axioms local_entry_of_startup
#print axioms output_after_entry
#print axioms startup_output
#print axioms later_output
#print axioms forward_safety_of_certificates
end AIFSafety.SafetyComposition
