import AIFSafety.CandidateMesh
import AIFSafety.TerminalEnergy
import Gimle.Forseti.RationalLDL

/-! Terminal entry for candidate bin 6, slab369, with exact checked premises.
This does not assert that a zero-start trajectory reaches this terminal tube. -/
namespace AIFSafety.TerminalEntryBin6
open Gimle.Forseti Gimle.Forseti.Examples
open Gimle.Forseti.LinearEnergy AIFLocalEntry TerminalEnergy

noncomputable def slab : AIFSlabModel.Slab := CandidateMesh.mesh.slab 6 369
noncomputable def certificate : WeightedSquares 4 :=
  Gimle.Forseti.RationalLDL.propose (coercivityMargin slab.endMetric)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem valid : certificate.Represents (coercivityMargin slab.endMetric) := by
  unfold WeightedSquares.Represents
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem lo_bound : rationalValue slab.loEnd ≤ 1/400 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem hi_bound : rationalValue slab.hiEnd ≤ 1/400 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem end_time : slab.tStart+slab.step=30 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem step_nonzero : slab.step ≠ 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem eta_order : slab.etaLo < slab.etaHi := by decide +kernel

/-- Membership in this exact candidate mesh cell at time 30 implies local entry. -/
theorem entry_at_thirty (eta : ℝ)
    (heta : eta ∈ Set.Icc ((CandidateMesh.mesh.slab 6 369).etaLo : ℝ)
      ((CandidateMesh.mesh.slab 6 369).etaHi : ℝ))
    (x : Fin 4 → ℝ)
    (tube : AIFMesh.tubeEnergy (CandidateMesh.mesh.slab 6 369) 30 eta x ≤ 1/40000) :
    value x ≤ 3/400 ∧ value x < 1/100 := by
  have ht : (slab.tStart : ℝ)+slab.step=30 := by exact_mod_cast end_time
  apply terminal_entry_physical slab step_nonzero eta_order certificate valid
    (real_bound _ lo_bound) (real_bound _ hi_bound) eta heta x
  rw [ht]
  simpa only [slab] using tube

#print axioms valid
#print axioms lo_bound
#print axioms hi_bound
#print axioms end_time
#print axioms step_nonzero
#print axioms eta_order
#print axioms entry_at_thirty
end AIFSafety.TerminalEntryBin6
