import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin2.Slab81
import AIFSafety.Cells.Bin2.Slab82
import AIFSafety.Cells.Bin2.Slab83
import AIFSafety.Cells.Bin2.Slab84
import AIFSafety.Cells.Bin2.Slab85
import AIFSafety.Cells.Bin2.Slab86
import AIFSafety.Cells.Bin2.Slab87
import AIFSafety.Cells.Bin2.Slab88
import AIFSafety.Cells.Bin2.Slab89
import AIFSafety.Cells.Bin2.Slab90
import AIFSafety.Cells.Bin2.Slab91
import AIFSafety.Cells.Bin2.Slab92
import AIFSafety.Cells.Bin2.Slab93
import AIFSafety.Cells.Bin2.Slab94
import AIFSafety.Cells.Bin2.Slab95
import AIFSafety.Cells.Bin2.Slab96
import AIFSafety.Cells.Bin2.Slab97
import AIFSafety.Cells.Bin2.Slab98
import AIFSafety.Cells.Bin2.Slab99
import AIFSafety.Cells.Bin2.Slab100
import AIFSafety.Cells.Bin2.Slab101
import AIFSafety.Cells.Bin2.Slab102
import AIFSafety.Cells.Bin2.Slab103
import AIFSafety.Cells.Bin2.Slab104
import AIFSafety.Cells.Bin2.Slab105
import AIFSafety.Cells.Bin2.Slab106
import AIFSafety.Cells.Bin2.Slab107
import AIFSafety.Cells.Bin2.Slab108
import AIFSafety.Cells.Bin2.Slab109
import AIFSafety.Cells.Bin2.Slab110
import AIFSafety.Cells.Bin2.Slab111
import AIFSafety.Cells.Bin2.Slab112
import AIFSafety.Cells.Bin2.Slab113
import AIFSafety.Cells.Bin2.Slab114
import AIFSafety.Cells.Bin2.Slab115
import AIFSafety.Cells.Bin2.Slab116
import AIFSafety.Cells.Bin2.Slab117
import AIFSafety.Cells.Bin2.Slab118
import AIFSafety.Cells.Bin2.Slab119
import AIFSafety.Cells.Bin2.Slab120

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin2Slabs81To120
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 40) :
    StartupPrefix.CellDrift 2 ⟨81 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin2.Slab81.drift_in_mesh
  · exact Cells.Bin2.Slab82.drift_in_mesh
  · exact Cells.Bin2.Slab83.drift_in_mesh
  · exact Cells.Bin2.Slab84.drift_in_mesh
  · exact Cells.Bin2.Slab85.drift_in_mesh
  · exact Cells.Bin2.Slab86.drift_in_mesh
  · exact Cells.Bin2.Slab87.drift_in_mesh
  · exact Cells.Bin2.Slab88.drift_in_mesh
  · exact Cells.Bin2.Slab89.drift_in_mesh
  · exact Cells.Bin2.Slab90.drift_in_mesh
  · exact Cells.Bin2.Slab91.drift_in_mesh
  · exact Cells.Bin2.Slab92.drift_in_mesh
  · exact Cells.Bin2.Slab93.drift_in_mesh
  · exact Cells.Bin2.Slab94.drift_in_mesh
  · exact Cells.Bin2.Slab95.drift_in_mesh
  · exact Cells.Bin2.Slab96.drift_in_mesh
  · exact Cells.Bin2.Slab97.drift_in_mesh
  · exact Cells.Bin2.Slab98.drift_in_mesh
  · exact Cells.Bin2.Slab99.drift_in_mesh
  · exact Cells.Bin2.Slab100.drift_in_mesh
  · exact Cells.Bin2.Slab101.drift_in_mesh
  · exact Cells.Bin2.Slab102.drift_in_mesh
  · exact Cells.Bin2.Slab103.drift_in_mesh
  · exact Cells.Bin2.Slab104.drift_in_mesh
  · exact Cells.Bin2.Slab105.drift_in_mesh
  · exact Cells.Bin2.Slab106.drift_in_mesh
  · exact Cells.Bin2.Slab107.drift_in_mesh
  · exact Cells.Bin2.Slab108.drift_in_mesh
  · exact Cells.Bin2.Slab109.drift_in_mesh
  · exact Cells.Bin2.Slab110.drift_in_mesh
  · exact Cells.Bin2.Slab111.drift_in_mesh
  · exact Cells.Bin2.Slab112.drift_in_mesh
  · exact Cells.Bin2.Slab113.drift_in_mesh
  · exact Cells.Bin2.Slab114.drift_in_mesh
  · exact Cells.Bin2.Slab115.drift_in_mesh
  · exact Cells.Bin2.Slab116.drift_in_mesh
  · exact Cells.Bin2.Slab117.drift_in_mesh
  · exact Cells.Bin2.Slab118.drift_in_mesh
  · exact Cells.Bin2.Slab119.drift_in_mesh
  · exact Cells.Bin2.Slab120.drift_in_mesh

theorem output (i : Fin 40) :
    SafetyComposition.CellOutput 2 ⟨81 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin2.Slab81.shifted_output_in_mesh
  · exact Cells.Bin2.Slab82.shifted_output_in_mesh
  · exact Cells.Bin2.Slab83.shifted_output_in_mesh
  · exact Cells.Bin2.Slab84.shifted_output_in_mesh
  · exact Cells.Bin2.Slab85.shifted_output_in_mesh
  · exact Cells.Bin2.Slab86.shifted_output_in_mesh
  · exact Cells.Bin2.Slab87.shifted_output_in_mesh
  · exact Cells.Bin2.Slab88.shifted_output_in_mesh
  · exact Cells.Bin2.Slab89.shifted_output_in_mesh
  · exact Cells.Bin2.Slab90.shifted_output_in_mesh
  · exact Cells.Bin2.Slab91.shifted_output_in_mesh
  · exact Cells.Bin2.Slab92.shifted_output_in_mesh
  · exact Cells.Bin2.Slab93.shifted_output_in_mesh
  · exact Cells.Bin2.Slab94.shifted_output_in_mesh
  · exact Cells.Bin2.Slab95.shifted_output_in_mesh
  · exact Cells.Bin2.Slab96.shifted_output_in_mesh
  · exact Cells.Bin2.Slab97.shifted_output_in_mesh
  · exact Cells.Bin2.Slab98.shifted_output_in_mesh
  · exact Cells.Bin2.Slab99.shifted_output_in_mesh
  · exact Cells.Bin2.Slab100.shifted_output_in_mesh
  · exact Cells.Bin2.Slab101.shifted_output_in_mesh
  · exact Cells.Bin2.Slab102.shifted_output_in_mesh
  · exact Cells.Bin2.Slab103.shifted_output_in_mesh
  · exact Cells.Bin2.Slab104.shifted_output_in_mesh
  · exact Cells.Bin2.Slab105.shifted_output_in_mesh
  · exact Cells.Bin2.Slab106.shifted_output_in_mesh
  · exact Cells.Bin2.Slab107.shifted_output_in_mesh
  · exact Cells.Bin2.Slab108.shifted_output_in_mesh
  · exact Cells.Bin2.Slab109.shifted_output_in_mesh
  · exact Cells.Bin2.Slab110.shifted_output_in_mesh
  · exact Cells.Bin2.Slab111.shifted_output_in_mesh
  · exact Cells.Bin2.Slab112.shifted_output_in_mesh
  · exact Cells.Bin2.Slab113.shifted_output_in_mesh
  · exact Cells.Bin2.Slab114.shifted_output_in_mesh
  · exact Cells.Bin2.Slab115.shifted_output_in_mesh
  · exact Cells.Bin2.Slab116.shifted_output_in_mesh
  · exact Cells.Bin2.Slab117.shifted_output_in_mesh
  · exact Cells.Bin2.Slab118.shifted_output_in_mesh
  · exact Cells.Bin2.Slab119.shifted_output_in_mesh
  · exact Cells.Bin2.Slab120.shifted_output_in_mesh


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin2Slabs81To120
