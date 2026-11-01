import AIFSafety.StartupPrefix
import AIFSafety.Cells.Bin0.Slab0
import AIFSafety.Cells.Bin7.Slab0
import AIFSafety.Cells.Bin1.Slab0
import AIFSafety.Cells.Bin2.Slab0
import AIFSafety.Cells.Bin3.Slab0
import AIFSafety.Cells.Bin4.Slab0
import AIFSafety.Cells.Bin5.Slab0
import AIFSafety.Cells.Bin6.Slab0
import AIFSafety.Cells.Bin0.Slab1
import AIFSafety.Cells.Bin0.Slab2
import AIFSafety.Cells.Bin0.Slab3
import AIFSafety.Cells.Bin0.Slab4
import AIFSafety.Cells.Bin0.Slab5
import AIFSafety.Cells.Bin0.Slab6
import AIFSafety.Cells.Bin0.Slab7
import AIFSafety.Cells.Bin0.Slab8
import AIFSafety.Cells.Bin0.Slab9
import AIFSafety.Cells.Bin0.Slab10
import AIFSafety.Cells.Bin0.Slab11
import AIFSafety.Cells.Bin0.Slab12
import AIFSafety.Cells.Bin0.Slab13
import AIFSafety.Cells.Bin0.Slab14
import AIFSafety.Cells.Bin0.Slab15
import AIFSafety.Cells.Bin0.Slab16
import AIFSafety.Cells.Bin0.Slab17
import AIFSafety.Cells.Bin0.Slab18
import AIFSafety.Cells.Bin0.Slab19
import AIFSafety.Cells.Bin0.Slab20

/-! Physical compiled-output safety on checked startup prefixes, for every
realization of the circuit. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.StartupOutput
open Gimle.Forseti Gimle.Forseti.Examples
open AIFMesh AIFSlabModel AIFPhysicalCoordinates

/-- Every first-slab bin supplies a checked output enclosure. -/
theorem first_cell_output (b : Fin 8) (t eta : ℝ) (x : Fin 4 → ℝ)
    (ht : t ∈ Set.Icc ((CandidateMesh.mesh.slab b 0).tStart : ℝ)
      (((CandidateMesh.mesh.slab b 0).tStart : ℝ) + (CandidateMesh.mesh.slab b 0).step))
    (hp : eta ∈ Set.Icc ((CandidateMesh.mesh.slab b 0).etaLo : ℝ)
      ((CandidateMesh.mesh.slab b 0).etaHi : ℝ))
    (he : tubeEnergy (CandidateMesh.mesh.slab b 0) t eta x ≤ 1/40000) :
    x 1 ≤ 6/5 := by
  fin_cases b
  · exact Cells.Bin0.Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin1.Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin2.Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin3.Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin4.Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin5.Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin6.Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin7.Slab0.shifted_output_in_mesh t eta x ht hp he

/-- All 21 cells of the first bin supply checked output enclosures. -/
theorem bin0_cell_output (i : Fin 21) (t eta : ℝ) (x : Fin 4 → ℝ)
    (ht : t ∈ Set.Icc
      ((CandidateMesh.mesh.slab 0 ⟨i.val, by omega⟩).tStart : ℝ)
      (((CandidateMesh.mesh.slab 0 ⟨i.val, by omega⟩).tStart : ℝ) +
        (CandidateMesh.mesh.slab 0 ⟨i.val, by omega⟩).step))
    (hp : eta ∈ Set.Icc (MeshGeometry.edges 0 : ℝ) (MeshGeometry.edges 1 : ℝ))
    (he : tubeEnergy (CandidateMesh.mesh.slab 0 ⟨i.val, by omega⟩) t eta x ≤ 1/40000) :
    x 1 ≤ 6/5 := by
  fin_cases i
  · exact Cells.Bin0.Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab1.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab2.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab3.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab4.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab5.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab6.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab7.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab8.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab9.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab10.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab11.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab12.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab13.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab14.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab15.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab16.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab17.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab18.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab19.shifted_output_in_mesh t eta x ht hp he
  · exact Cells.Bin0.Slab20.shifted_output_in_mesh t eta x ht hp he

/-- Physical x2 safety over the first closed slab in any fixed parameter bin. -/
theorem first_slab_output (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (MeshGeometry.edges b.castSucc : ℝ)
      (MeshGeometry.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/200)) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  apply (AIFCircuitBinding.compiled_output_bound_iff eta (state t)).mpr
  apply first_cell_output b t eta (shift eta (state t)) _ hp
    (StartupPrefix.first_slab_invariant b eta hp state realized t ht)
  have ht1q : CandidateMesh.mesh.times 1 = 1/200 := by decide +kernel
  have ht1 : (CandidateMesh.mesh.times 1 : ℝ) = 1/200 := by
    rw [ht1q]
    norm_num
  have ht' : t ∈ Set.Icc (CandidateMesh.mesh.times 0 : ℝ)
      (CandidateMesh.mesh.times 1 : ℝ) := by
    rw [StartupInitial.time_zero, ht1]
    simpa only [Rat.cast_zero] using ht
  simpa only [Mesh.slab, Rat.cast_sub, add_sub_cancel, Fin.castSucc_zero, Fin.succ_zero_eq_one] using ht'

/-- Physical x2 stays at most 16/5 through time 1/200 for every eta in [8,12]. -/
theorem all_parameter_output (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/200)) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  obtain ⟨b, hb⟩ := AIFMesh.interval_covered 7
    (fun j => (MeshGeometry.edges j : ℝ)) eta
    (by simpa [MeshGeometry.edges] using hp)
  exact first_slab_output b eta hb state realized t ht

/-- Physical x2 stays at most 16/5 through time 21/200 for eta in [8,17/2]. -/
theorem bin0_prefix_output (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) (17/2))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (21/200)) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  obtain ⟨i, hi, he⟩ := StartupPrefix.bin0_prefix_invariant eta hp state realized t ht
  apply (AIFCircuitBinding.compiled_output_bound_iff eta (state t)).mpr
  apply bin0_cell_output i t eta (shift eta (state t)) _ _ he
  · change t ∈ Set.Icc
      (CandidateMesh.mesh.times (⟨i.val, by omega⟩ : Fin 370).castSucc : ℝ)
      (CandidateMesh.mesh.times (⟨i.val, by omega⟩ : Fin 370).succ : ℝ) at hi
    simpa only [Mesh.slab, Rat.cast_sub, add_sub_cancel] using hi
  · simpa [MeshGeometry.edges] using hp

#print axioms first_cell_output
#print axioms bin0_cell_output
#print axioms first_slab_output
#print axioms all_parameter_output
#print axioms bin0_prefix_output
end AIFSafety.StartupOutput
