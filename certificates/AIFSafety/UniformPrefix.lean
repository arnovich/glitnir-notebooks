import AIFSafety.SafetyComposition
import AIFSafety.UniformPrefixBin1
import AIFSafety.UniformPrefixBin2
import AIFSafety.UniformPrefixBin3
import AIFSafety.UniformPrefixBin4
import AIFSafety.UniformPrefixBin5
import AIFSafety.UniformPrefixBin6
import AIFSafety.UniformPrefixBin7

/-! Nonempty actual compiled-circuit safety on [0,21/200] for all eta in [8,12].
All 168 prefix cells supply checked drift and output certificates. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.UniformPrefix
open Gimle.Forseti Gimle.Forseti.Examples
open AIFMesh AIFSlabModel AIFPhysicalCoordinates StartupPrefix

theorem drift (b : Fin 8) (i : Fin 21) : CellDrift b ⟨i.val, by omega⟩ := by
  fin_cases b
  · exact bin0_drift i
  · exact UniformPrefixBin1.drift i
  · exact UniformPrefixBin2.drift i
  · exact UniformPrefixBin3.drift i
  · exact UniformPrefixBin4.drift i
  · exact UniformPrefixBin5.drift i
  · exact UniformPrefixBin6.drift i
  · exact UniformPrefixBin7.drift i

theorem output (b : Fin 8) (i : Fin 21) :
    SafetyComposition.CellOutput b ⟨i.val, by omega⟩ := by
  fin_cases b
  · exact StartupOutput.bin0_cell_output i
  · exact UniformPrefixBin1.output i
  · exact UniformPrefixBin2.output i
  · exact UniformPrefixBin3.output i
  · exact UniformPrefixBin4.output i
  · exact UniformPrefixBin5.output i
  · exact UniformPrefixBin6.output i
  · exact UniformPrefixBin7.output i

theorem membership (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (MeshGeometry.edges b.castSucc : ℝ)
      (MeshGeometry.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (i : Fin 21) (t : ℝ)
    (ht : t ∈ Set.Icc ((prefixMesh 21 (by decide)).times i.castSucc : ℝ)
      ((prefixMesh 21 (by decide)).times i.succ : ℝ)) :
    tubeEnergy ((prefixMesh 21 (by decide)).slab b i) t eta
      (shift eta (state t)) ≤ 1/40000 :=
  prefix_invariant 20 (by decide) b eta hp state realized (drift b) i t ht

theorem bin_output (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (MeshGeometry.edges b.castSucc : ℝ)
      (MeshGeometry.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (21/200)) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  have ht' : t ∈ Set.Icc ((prefixMesh 21 (by decide)).times 0 : ℝ)
      ((prefixMesh 21 (by decide)).times 21 : ℝ) := by
    change t ∈ Set.Icc (CandidateMesh.mesh.times 0 : ℝ)
      ((prefixMesh 21 (by decide)).times 21 : ℝ)
    rw [StartupInitial.time_zero, bin0_endpoint]
    norm_num at *
    exact ht
  obtain ⟨i, hi, he⟩ := AIFMeshComposition.covered_energy
    (prefixMesh 21 (by decide)) b eta (fun s => shift eta (state s))
    (membership b eta hp state realized) t ht'
  apply (AIFCircuitBinding.compiled_output_bound_iff eta (state t)).mpr
  apply output b i t eta (shift eta (state t)) _ hp he
  change t ∈ Set.Icc
    (CandidateMesh.mesh.times (⟨i.val, by omega⟩ : Fin 370).castSucc : ℝ)
    (CandidateMesh.mesh.times (⟨i.val, by omega⟩ : Fin 370).succ : ℝ) at hi
  simpa only [Mesh.slab, Rat.cast_sub, add_sub_cancel] using hi

theorem all_parameter_output (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (21/200)) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  obtain ⟨b, hb⟩ := AIFMesh.interval_covered 7
    (fun j => (MeshGeometry.edges j : ℝ)) eta
    (by simpa [MeshGeometry.edges] using hp)
  exact bin_output b eta hb state realized t ht

/-- Existence plus universal safety, with no tube or cell-certificate premises. -/
theorem all_parameter_safety (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    (∃ state, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    ∀ state, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Icc (0 : ℝ) (21/200),
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  have heta : 0 ≤ eta := by linarith [hp.1]
  refine ⟨AIFCircuitBinding.exists_realization eta heta, ?_⟩
  intro state realized t ht
  exact ⟨AIFCircuitBinding.realization_output_nonnegative eta heta state realized t ht.1,
    all_parameter_output eta hp state realized t ht⟩

#print axioms drift
#print axioms output
#print axioms membership
#print axioms bin_output
#print axioms all_parameter_output
#print axioms all_parameter_safety
end AIFSafety.UniformPrefix
