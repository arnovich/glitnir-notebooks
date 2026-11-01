import AIFSafety.Cell
import AIFSafety.CandidateMesh

/-! Cell (3, 229) of the AIF moving tube: eta bin 3, time slab 229. Its slab is
the candidate mesh's cell; the kernel computes and checks everything else: the
drift-block Bernstein tables and their square certificates, and the containment
and output margins. -/
namespace AIFSafety.Cells.Bin3.Slab229

noncomputable abbrev slab := CandidateMesh.mesh.slab 3 229

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem negative : Cell.BlockCheck slab (-3/200) := by
  unfold Cell.BlockCheck Gimle.Forseti.LinearEnergy.WeightedSquares.Represents
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem positive : Cell.BlockCheck slab (3/200) := by
  unfold Cell.BlockCheck Gimle.Forseti.LinearEnergy.WeightedSquares.Represents
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem containment : Cell.ContainmentCheck slab := by
  unfold Cell.ContainmentCheck Gimle.Forseti.LinearEnergy.WeightedSquares.Represents
  decide +kernel

theorem symmetric : Gimle.Forseti.Examples.AIFSlabData.SymmetricData slab := by
  unfold Gimle.Forseti.Examples.AIFSlabData.SymmetricData
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem output : Cell.OutputCheck slab := by
  unfold Cell.OutputCheck Gimle.Forseti.LinearEnergy.WeightedSquares.Represents
  decide +kernel

theorem width : 0 < slab.step := by decide +kernel

theorem ordered : slab.etaLo < slab.etaHi := by decide +kernel

theorem drift_in_mesh : Cell.Drift (CandidateMesh.mesh.slab 3 229) :=
  Cell.drift slab negative positive containment symmetric width ordered

theorem shifted_output_in_mesh : Cell.Output (CandidateMesh.mesh.slab 3 229) :=
  Cell.output slab output width ordered

#print axioms drift_in_mesh
#print axioms shifted_output_in_mesh
end AIFSafety.Cells.Bin3.Slab229
