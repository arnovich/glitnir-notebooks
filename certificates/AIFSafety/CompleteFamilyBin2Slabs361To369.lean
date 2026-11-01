import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin2.Slab361
import AIFSafety.Cells.Bin2.Slab362
import AIFSafety.Cells.Bin2.Slab363
import AIFSafety.Cells.Bin2.Slab364
import AIFSafety.Cells.Bin2.Slab365
import AIFSafety.Cells.Bin2.Slab366
import AIFSafety.Cells.Bin2.Slab367
import AIFSafety.Cells.Bin2.Slab368
import AIFSafety.Cells.Bin2.Slab369

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin2Slabs361To369
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 9) :
    StartupPrefix.CellDrift 2 ⟨361 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin2.Slab361.drift_in_mesh
  · exact Cells.Bin2.Slab362.drift_in_mesh
  · exact Cells.Bin2.Slab363.drift_in_mesh
  · exact Cells.Bin2.Slab364.drift_in_mesh
  · exact Cells.Bin2.Slab365.drift_in_mesh
  · exact Cells.Bin2.Slab366.drift_in_mesh
  · exact Cells.Bin2.Slab367.drift_in_mesh
  · exact Cells.Bin2.Slab368.drift_in_mesh
  · exact Cells.Bin2.Slab369.drift_in_mesh

theorem output (i : Fin 9) :
    SafetyComposition.CellOutput 2 ⟨361 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin2.Slab361.shifted_output_in_mesh
  · exact Cells.Bin2.Slab362.shifted_output_in_mesh
  · exact Cells.Bin2.Slab363.shifted_output_in_mesh
  · exact Cells.Bin2.Slab364.shifted_output_in_mesh
  · exact Cells.Bin2.Slab365.shifted_output_in_mesh
  · exact Cells.Bin2.Slab366.shifted_output_in_mesh
  · exact Cells.Bin2.Slab367.shifted_output_in_mesh
  · exact Cells.Bin2.Slab368.shifted_output_in_mesh
  · exact Cells.Bin2.Slab369.shifted_output_in_mesh


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin2Slabs361To369
