import Gimle.Forseti.Examples.AIFCircuitBinding
import AIFSafety.StartupInitial
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

/-! Tube invariance on the startup prefixes of the compiled circuit, from the
checked drift proofs of the cells they contain. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.StartupPrefix
open Gimle.Forseti Gimle.Forseti.Examples
open AIFMesh AIFSlabModel AIFPhysicalCoordinates Gimle.Forseti.BernsteinMatrix

noncomputable def prefixMesh (n : Nat) (hn : n ≤ 370) : Mesh n 8 where
  times i := CandidateMesh.mesh.times ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hn)⟩
  edges := CandidateMesh.mesh.edges
  nodes b i := CandidateMesh.mesh.nodes b ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hn)⟩

theorem prefix_slab (n : Nat) (hn : n ≤ 370) (b : Fin 8) (i : Fin n) :
    (prefixMesh n hn).slab b i =
      CandidateMesh.mesh.slab b ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ := rfl

theorem times_nonnegative : ∀ i : Fin 371, 0 ≤ MeshGeometry.times i := by
  decide +kernel

/-- A checked drift obligation for one concrete full-mesh cell. -/
def CellDrift (b : Fin 8) (i : Fin 370) : Prop :=
  ∀ t p (e : Fin 4 → ℝ),
    t ∈ Set.Icc ((CandidateMesh.mesh.slab b i).tStart : ℝ)
      (((CandidateMesh.mesh.slab b i).tStart : ℝ) + (CandidateMesh.mesh.slab b i).step) →
    p ∈ Set.Icc ((CandidateMesh.mesh.slab b i).etaLo : ℝ)
      ((CandidateMesh.mesh.slab b i).etaHi : ℝ) →
    matrixForm (metric (CandidateMesh.mesh.slab b i)
      (timeCoordinate (CandidateMesh.mesh.slab b i) t)) e ≤ 1/40000 →
    energyRate (CandidateMesh.mesh.slab b i)
      (timeCoordinate (CandidateMesh.mesh.slab b i) t)
      (etaCoordinate (CandidateMesh.mesh.slab b i) p) e ≤
      (1/100) * (1/40000 - matrixForm (metric (CandidateMesh.mesh.slab b i)
        (timeCoordinate (CandidateMesh.mesh.slab b i) t)) e) - 1/16000000

/-- Every prefix cell must supply its own checked drift result. -/
theorem prefix_invariant (n : Nat) (hn : n + 1 ≤ 370) (b : Fin 8)
    (eta : ℝ) (hp : eta ∈ Set.Icc ((prefixMesh (n+1) hn).edges b.castSucc : ℝ)
      ((prefixMesh (n+1) hn).edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (drift : ∀ i : Fin (n+1), CellDrift b ⟨i.val, lt_of_lt_of_le i.isLt hn⟩) :
    ∀ i, ∀ t ∈ Set.Icc ((prefixMesh (n+1) hn).times i.castSucc : ℝ)
      ((prefixMesh (n+1) hn).times i.succ : ℝ),
      tubeEnergy ((prefixMesh (n+1) hn).slab b i) t eta (shift eta (state t)) ≤ 1/40000 := by
  apply AIFMeshComposition.mesh_invariant (prefixMesh (n+1) hn) b
  · intro i
    rw [prefix_slab]
    exact MeshGeometry.step_positive CandidateMesh.nodes b _
  · exact MeshGeometry.eta_positive b
  · exact hp
  · intro i t ht j
    apply AIFCircuitBinding.shifted_derivative_on eta state realized _ _ _ t ht j
    exact_mod_cast times_nonnegative ⟨i.val, by omega⟩
  · intro i t p e ht hparam he
    apply drift i t p e
    · change t ∈ Set.Icc
        (CandidateMesh.mesh.times (⟨i.val, lt_of_lt_of_le i.isLt hn⟩ : Fin 370).castSucc : ℝ)
        (CandidateMesh.mesh.times (⟨i.val, lt_of_lt_of_le i.isLt hn⟩ : Fin 370).succ : ℝ) at ht
      simpa only [Mesh.slab, Rat.cast_sub, add_sub_cancel] using ht
    · exact hparam
    · exact he
  · have hz : ((prefixMesh (n+1) hn).times 0 : ℝ) = 0 := by
      change (CandidateMesh.mesh.times 0 : ℝ) = 0
      rw [StartupInitial.time_zero]
      norm_num
    rw [hz, AIFCircuitBinding.shifted_initial eta state realized]
    have hi := StartupInitial.initial_energy b eta
    have hs : (fun i => (StartupInitial.shiftedInitial i : ℝ)) = ![-2,-2,-2,-1] := by
      ext i
      fin_cases i <;> norm_num [StartupInitial.shiftedInitial]
    rw [hs] at hi
    change tubeEnergy (CandidateMesh.mesh.slab b 0) 0 eta ![-2,-2,-2,-1] ≤ 1/40000
    rw [hi]
    norm_num

theorem first_drift (b : Fin 8) : CellDrift b 0 := by
  fin_cases b
  · exact Cells.Bin0.Slab0.drift_in_mesh
  · exact Cells.Bin1.Slab0.drift_in_mesh
  · exact Cells.Bin2.Slab0.drift_in_mesh
  · exact Cells.Bin3.Slab0.drift_in_mesh
  · exact Cells.Bin4.Slab0.drift_in_mesh
  · exact Cells.Bin5.Slab0.drift_in_mesh
  · exact Cells.Bin6.Slab0.drift_in_mesh
  · exact Cells.Bin7.Slab0.drift_in_mesh

theorem bin0_drift (i : Fin 21) : CellDrift 0 ⟨i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin0.Slab0.drift_in_mesh
  · exact Cells.Bin0.Slab1.drift_in_mesh
  · exact Cells.Bin0.Slab2.drift_in_mesh
  · exact Cells.Bin0.Slab3.drift_in_mesh
  · exact Cells.Bin0.Slab4.drift_in_mesh
  · exact Cells.Bin0.Slab5.drift_in_mesh
  · exact Cells.Bin0.Slab6.drift_in_mesh
  · exact Cells.Bin0.Slab7.drift_in_mesh
  · exact Cells.Bin0.Slab8.drift_in_mesh
  · exact Cells.Bin0.Slab9.drift_in_mesh
  · exact Cells.Bin0.Slab10.drift_in_mesh
  · exact Cells.Bin0.Slab11.drift_in_mesh
  · exact Cells.Bin0.Slab12.drift_in_mesh
  · exact Cells.Bin0.Slab13.drift_in_mesh
  · exact Cells.Bin0.Slab14.drift_in_mesh
  · exact Cells.Bin0.Slab15.drift_in_mesh
  · exact Cells.Bin0.Slab16.drift_in_mesh
  · exact Cells.Bin0.Slab17.drift_in_mesh
  · exact Cells.Bin0.Slab18.drift_in_mesh
  · exact Cells.Bin0.Slab19.drift_in_mesh
  · exact Cells.Bin0.Slab20.drift_in_mesh

theorem first_endpoint : (prefixMesh 1 (by decide)).times 1 = 1/200 := by decide +kernel

theorem bin0_endpoint : (prefixMesh 21 (by decide)).times 21 = 21/200 := by decide +kernel

/-- All eight parameter bins have an invariant first closed time slab. -/
theorem first_slab_invariant (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (MeshGeometry.edges b.castSucc : ℝ)
      (MeshGeometry.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/200)) :
    tubeEnergy (CandidateMesh.mesh.slab b 0) t eta (shift eta (state t)) ≤ 1/40000 := by
  have h := prefix_invariant 0 (by decide) b eta hp state realized
    (fun i => by fin_cases i; exact first_drift b) 0 t
  apply h
  change t ∈ Set.Icc (CandidateMesh.mesh.times 0 : ℝ) ((prefixMesh 1 (by decide)).times 1 : ℝ)
  rw [StartupInitial.time_zero, first_endpoint]
  norm_num at *
  exact ht

/-- The first closed startup interval is covered for every parameter in [8,12]. -/
theorem all_parameter_startup (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state) :
    ∃ b : Fin 8, ∀ t ∈ Set.Icc (0 : ℝ) (1/200),
      tubeEnergy (CandidateMesh.mesh.slab b 0) t eta (shift eta (state t)) ≤ 1/40000 := by
  obtain ⟨b, hb⟩ := AIFMesh.interval_covered 7
    (fun j => (MeshGeometry.edges j : ℝ)) eta
    (by simpa [MeshGeometry.edges] using hp)
  exact ⟨b, fun t ht => first_slab_invariant b eta hb state realized t ht⟩

/-- A fixed parameter in [8,17/2] stays in the moving tube for all 21 startup cells. -/
theorem bin0_prefix_invariant (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) (17/2))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (21/200)) :
    ∃ i : Fin 21,
      t ∈ Set.Icc ((prefixMesh 21 (by decide)).times i.castSucc : ℝ)
        ((prefixMesh 21 (by decide)).times i.succ : ℝ) ∧
      tubeEnergy ((prefixMesh 21 (by decide)).slab 0 i) t eta (shift eta (state t)) ≤ 1/40000 := by
  apply AIFMeshComposition.covered_energy (prefixMesh 21 (by decide)) 0 eta
    (fun s => shift eta (state s))
  · apply prefix_invariant 20 (by decide) 0 eta _ state realized bin0_drift
    simpa [prefixMesh, CandidateMesh.mesh, MeshGeometry.mesh, MeshGeometry.edges] using hp
  · change t ∈ Set.Icc (CandidateMesh.mesh.times 0 : ℝ) ((prefixMesh 21 (by decide)).times 21 : ℝ)
    rw [StartupInitial.time_zero, bin0_endpoint]
    norm_num at *
    exact ht

#print axioms prefix_slab
#print axioms times_nonnegative
#print axioms prefix_invariant
#print axioms first_drift
#print axioms bin0_drift
#print axioms first_endpoint
#print axioms bin0_endpoint
#print axioms first_slab_invariant
#print axioms all_parameter_startup
#print axioms bin0_prefix_invariant
end AIFSafety.StartupPrefix
