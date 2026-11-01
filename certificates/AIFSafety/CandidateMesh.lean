import AIFSafety.MeshGeometry
import AIFSafety.MeshBin0
import AIFSafety.MeshBin1
import AIFSafety.MeshBin2
import AIFSafety.MeshBin3
import AIFSafety.MeshBin4
import AIFSafety.MeshBin5
import AIFSafety.MeshBin6
import AIFSafety.MeshBin7

/-! The candidate mesh: all eight bins, coverage and joins.
The mesh is untrusted numerical data: the kernel checks every fact the proof
uses about it. Candidate SHA-256, for provenance only:
96c882a6183ef5cd7e42e517092e50d0a78358a378dd94390241ffa4b92f2c39. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CandidateMesh
open Gimle.Forseti Gimle.Forseti.Examples
open AIFMesh AIFSlabModel
open Gimle.Forseti.BernsteinMatrix

noncomputable def nodes : Fin 8 → Fin 371 → Knot := ![MeshBin0.nodes, MeshBin1.nodes, MeshBin2.nodes, MeshBin3.nodes, MeshBin4.nodes, MeshBin5.nodes, MeshBin6.nodes, MeshBin7.nodes]

noncomputable def mesh : Mesh 370 8 := MeshGeometry.mesh nodes

theorem covers (t p : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 30)
    (hp : p ∈ Set.Icc (8 : ℝ) 12) :
    ∃ b : Fin 8, ∃ i : Fin 370,
      t ∈ Set.Icc ((mesh.slab b i).tStart : ℝ)
        (((mesh.slab b i).tStart : ℝ) + (mesh.slab b i).step) ∧
      p ∈ Set.Icc ((mesh.slab b i).etaLo : ℝ) ((mesh.slab b i).etaHi : ℝ) :=
  MeshGeometry.covers nodes t p ht hp

theorem joins (b : Fin 8) (i : Fin 369) :
    Joins (mesh.slab b i.castSucc) (mesh.slab b i.succ) :=
  mesh.joins b i.castSucc i.succ rfl

theorem energy_join (b : Fin 8) (i : Fin 369) (p : ℝ) (x : Fin 4 → ℝ) :
    tubeEnergy (mesh.slab b i.castSucc) (mesh.slab b i.succ).tStart p x =
      tubeEnergy (mesh.slab b i.succ) (mesh.slab b i.succ).tStart p x :=
  (joins b i).tubeEnergy_eq
    (ne_of_gt (MeshGeometry.step_positive nodes b i.castSucc))
    (ne_of_gt (MeshGeometry.step_positive nodes b i.succ)) p x

theorem center_rate_join (b : Fin 8) (i : Fin 369) (u : ℝ) :
    centerRate (mesh.slab b i.castSucc) 1 u = centerRate (mesh.slab b i.succ) 0 u :=
  (joins b i).centerRate_eq
    (ne_of_gt (MeshGeometry.step_positive nodes b i.castSucc))
    (ne_of_gt (MeshGeometry.step_positive nodes b i.succ)) u

theorem metric_rate_join (b : Fin 8) (i : Fin 369) :
    metricRate (mesh.slab b i.castSucc) 1 = metricRate (mesh.slab b i.succ) 0 :=
  (joins b i).metricRate_eq
    (ne_of_gt (MeshGeometry.step_positive nodes b i.castSucc))
    (ne_of_gt (MeshGeometry.step_positive nodes b i.succ))

#print axioms covers
#print axioms joins
#print axioms energy_join
#print axioms center_rate_join
#print axioms metric_rate_join
end AIFSafety.CandidateMesh
