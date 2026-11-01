import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin5.Slab41
import AIFSafety.Cells.Bin5.Slab42
import AIFSafety.Cells.Bin5.Slab43
import AIFSafety.Cells.Bin5.Slab44
import AIFSafety.Cells.Bin5.Slab45
import AIFSafety.Cells.Bin5.Slab46
import AIFSafety.Cells.Bin5.Slab47
import AIFSafety.Cells.Bin5.Slab48
import AIFSafety.Cells.Bin5.Slab49
import AIFSafety.Cells.Bin5.Slab50
import AIFSafety.Cells.Bin5.Slab51
import AIFSafety.Cells.Bin5.Slab52
import AIFSafety.Cells.Bin5.Slab53
import AIFSafety.Cells.Bin5.Slab54
import AIFSafety.Cells.Bin5.Slab55
import AIFSafety.Cells.Bin5.Slab56
import AIFSafety.Cells.Bin5.Slab57
import AIFSafety.Cells.Bin5.Slab58
import AIFSafety.Cells.Bin5.Slab59
import AIFSafety.Cells.Bin5.Slab60
import AIFSafety.Cells.Bin5.Slab61
import AIFSafety.Cells.Bin5.Slab62
import AIFSafety.Cells.Bin5.Slab63
import AIFSafety.Cells.Bin5.Slab64
import AIFSafety.Cells.Bin5.Slab65
import AIFSafety.Cells.Bin5.Slab66
import AIFSafety.Cells.Bin5.Slab67
import AIFSafety.Cells.Bin5.Slab68
import AIFSafety.Cells.Bin5.Slab69
import AIFSafety.Cells.Bin5.Slab70
import AIFSafety.Cells.Bin5.Slab71
import AIFSafety.Cells.Bin5.Slab72
import AIFSafety.Cells.Bin5.Slab73
import AIFSafety.Cells.Bin5.Slab74
import AIFSafety.Cells.Bin5.Slab75
import AIFSafety.Cells.Bin5.Slab76
import AIFSafety.Cells.Bin5.Slab77
import AIFSafety.Cells.Bin5.Slab78
import AIFSafety.Cells.Bin5.Slab79
import AIFSafety.Cells.Bin5.Slab80

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin5Slabs41To80
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 40) :
    StartupPrefix.CellDrift 5 ⟨41 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin5.Slab41.drift_in_mesh
  · exact Cells.Bin5.Slab42.drift_in_mesh
  · exact Cells.Bin5.Slab43.drift_in_mesh
  · exact Cells.Bin5.Slab44.drift_in_mesh
  · exact Cells.Bin5.Slab45.drift_in_mesh
  · exact Cells.Bin5.Slab46.drift_in_mesh
  · exact Cells.Bin5.Slab47.drift_in_mesh
  · exact Cells.Bin5.Slab48.drift_in_mesh
  · exact Cells.Bin5.Slab49.drift_in_mesh
  · exact Cells.Bin5.Slab50.drift_in_mesh
  · exact Cells.Bin5.Slab51.drift_in_mesh
  · exact Cells.Bin5.Slab52.drift_in_mesh
  · exact Cells.Bin5.Slab53.drift_in_mesh
  · exact Cells.Bin5.Slab54.drift_in_mesh
  · exact Cells.Bin5.Slab55.drift_in_mesh
  · exact Cells.Bin5.Slab56.drift_in_mesh
  · exact Cells.Bin5.Slab57.drift_in_mesh
  · exact Cells.Bin5.Slab58.drift_in_mesh
  · exact Cells.Bin5.Slab59.drift_in_mesh
  · exact Cells.Bin5.Slab60.drift_in_mesh
  · exact Cells.Bin5.Slab61.drift_in_mesh
  · exact Cells.Bin5.Slab62.drift_in_mesh
  · exact Cells.Bin5.Slab63.drift_in_mesh
  · exact Cells.Bin5.Slab64.drift_in_mesh
  · exact Cells.Bin5.Slab65.drift_in_mesh
  · exact Cells.Bin5.Slab66.drift_in_mesh
  · exact Cells.Bin5.Slab67.drift_in_mesh
  · exact Cells.Bin5.Slab68.drift_in_mesh
  · exact Cells.Bin5.Slab69.drift_in_mesh
  · exact Cells.Bin5.Slab70.drift_in_mesh
  · exact Cells.Bin5.Slab71.drift_in_mesh
  · exact Cells.Bin5.Slab72.drift_in_mesh
  · exact Cells.Bin5.Slab73.drift_in_mesh
  · exact Cells.Bin5.Slab74.drift_in_mesh
  · exact Cells.Bin5.Slab75.drift_in_mesh
  · exact Cells.Bin5.Slab76.drift_in_mesh
  · exact Cells.Bin5.Slab77.drift_in_mesh
  · exact Cells.Bin5.Slab78.drift_in_mesh
  · exact Cells.Bin5.Slab79.drift_in_mesh
  · exact Cells.Bin5.Slab80.drift_in_mesh

theorem output (i : Fin 40) :
    SafetyComposition.CellOutput 5 ⟨41 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin5.Slab41.shifted_output_in_mesh
  · exact Cells.Bin5.Slab42.shifted_output_in_mesh
  · exact Cells.Bin5.Slab43.shifted_output_in_mesh
  · exact Cells.Bin5.Slab44.shifted_output_in_mesh
  · exact Cells.Bin5.Slab45.shifted_output_in_mesh
  · exact Cells.Bin5.Slab46.shifted_output_in_mesh
  · exact Cells.Bin5.Slab47.shifted_output_in_mesh
  · exact Cells.Bin5.Slab48.shifted_output_in_mesh
  · exact Cells.Bin5.Slab49.shifted_output_in_mesh
  · exact Cells.Bin5.Slab50.shifted_output_in_mesh
  · exact Cells.Bin5.Slab51.shifted_output_in_mesh
  · exact Cells.Bin5.Slab52.shifted_output_in_mesh
  · exact Cells.Bin5.Slab53.shifted_output_in_mesh
  · exact Cells.Bin5.Slab54.shifted_output_in_mesh
  · exact Cells.Bin5.Slab55.shifted_output_in_mesh
  · exact Cells.Bin5.Slab56.shifted_output_in_mesh
  · exact Cells.Bin5.Slab57.shifted_output_in_mesh
  · exact Cells.Bin5.Slab58.shifted_output_in_mesh
  · exact Cells.Bin5.Slab59.shifted_output_in_mesh
  · exact Cells.Bin5.Slab60.shifted_output_in_mesh
  · exact Cells.Bin5.Slab61.shifted_output_in_mesh
  · exact Cells.Bin5.Slab62.shifted_output_in_mesh
  · exact Cells.Bin5.Slab63.shifted_output_in_mesh
  · exact Cells.Bin5.Slab64.shifted_output_in_mesh
  · exact Cells.Bin5.Slab65.shifted_output_in_mesh
  · exact Cells.Bin5.Slab66.shifted_output_in_mesh
  · exact Cells.Bin5.Slab67.shifted_output_in_mesh
  · exact Cells.Bin5.Slab68.shifted_output_in_mesh
  · exact Cells.Bin5.Slab69.shifted_output_in_mesh
  · exact Cells.Bin5.Slab70.shifted_output_in_mesh
  · exact Cells.Bin5.Slab71.shifted_output_in_mesh
  · exact Cells.Bin5.Slab72.shifted_output_in_mesh
  · exact Cells.Bin5.Slab73.shifted_output_in_mesh
  · exact Cells.Bin5.Slab74.shifted_output_in_mesh
  · exact Cells.Bin5.Slab75.shifted_output_in_mesh
  · exact Cells.Bin5.Slab76.shifted_output_in_mesh
  · exact Cells.Bin5.Slab77.shifted_output_in_mesh
  · exact Cells.Bin5.Slab78.shifted_output_in_mesh
  · exact Cells.Bin5.Slab79.shifted_output_in_mesh
  · exact Cells.Bin5.Slab80.shifted_output_in_mesh


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin5Slabs41To80
