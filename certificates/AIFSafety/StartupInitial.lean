import AIFSafety.CandidateMesh
import Gimle.Forseti.Examples.AIFMeshComposition

/-! The shifted zero start lies in the first tube, exactly. The change of
coordinates to the compiled circuit is `AIFPhysicalCoordinates.shift`. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.StartupInitial
open Gimle.Forseti Gimle.Forseti.Examples
open AIFSlabModel AIFMesh AIFMeshComposition

def shiftedInitial : Fin 4 → ℚ := ![-2,-2,-2,-1]

theorem time_zero : CandidateMesh.mesh.times 0 = 0 := by
  decide +kernel

theorem centers_initial : ∀ b : Fin 8,
    (CandidateMesh.mesh.slab b 0).loStart = shiftedInitial ∧
    (CandidateMesh.mesh.slab b 0).hiStart = shiftedInitial := by
  decide +kernel

theorem initial_energy (b : Fin 8) (p : ℝ) :
    tubeEnergy (CandidateMesh.mesh.slab b 0) 0 p
      (fun i => (shiftedInitial i : ℝ)) = 0 := by
  have h := initial_energy_of_centers (CandidateMesh.mesh.slab b 0) shiftedInitial
    (centers_initial b).1 (centers_initial b).2 p
  have ht : ((CandidateMesh.mesh.slab b 0).tStart : ℝ) = 0 := by
    change (CandidateMesh.mesh.times 0 : ℝ) = 0
    rw [time_zero]
    norm_num
  simpa only [ht] using h

#print axioms time_zero
#print axioms centers_initial
#print axioms initial_energy
end AIFSafety.StartupInitial
