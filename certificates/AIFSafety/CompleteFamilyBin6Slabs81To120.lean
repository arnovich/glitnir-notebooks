import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin6.Slab81
import AIFSafety.Cells.Bin6.Slab82
import AIFSafety.Cells.Bin6.Slab83
import AIFSafety.Cells.Bin6.Slab84
import AIFSafety.Cells.Bin6.Slab85
import AIFSafety.Cells.Bin6.Slab86
import AIFSafety.Cells.Bin6.Slab87
import AIFSafety.Cells.Bin6.Slab88
import AIFSafety.Cells.Bin6.Slab89
import AIFSafety.Cells.Bin6.Slab90
import AIFSafety.Cells.Bin6.Slab91
import AIFSafety.Cells.Bin6.Slab92
import AIFSafety.Cells.Bin6.Slab93
import AIFSafety.Cells.Bin6.Slab94
import AIFSafety.Cells.Bin6.Slab95
import AIFSafety.Cells.Bin6.Slab96
import AIFSafety.Cells.Bin6.Slab97
import AIFSafety.Cells.Bin6.Slab98
import AIFSafety.Cells.Bin6.Slab99
import AIFSafety.Cells.Bin6.Slab100
import AIFSafety.Cells.Bin6.Slab101
import AIFSafety.Cells.Bin6.Slab102
import AIFSafety.Cells.Bin6.Slab103
import AIFSafety.Cells.Bin6.Slab104
import AIFSafety.Cells.Bin6.Slab105
import AIFSafety.Cells.Bin6.Slab106
import AIFSafety.Cells.Bin6.Slab107
import AIFSafety.Cells.Bin6.Slab108
import AIFSafety.Cells.Bin6.Slab109
import AIFSafety.Cells.Bin6.Slab110
import AIFSafety.Cells.Bin6.Slab111
import AIFSafety.Cells.Bin6.Slab112
import AIFSafety.Cells.Bin6.Slab113
import AIFSafety.Cells.Bin6.Slab114
import AIFSafety.Cells.Bin6.Slab115
import AIFSafety.Cells.Bin6.Slab116
import AIFSafety.Cells.Bin6.Slab117
import AIFSafety.Cells.Bin6.Slab118
import AIFSafety.Cells.Bin6.Slab119
import AIFSafety.Cells.Bin6.Slab120

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin6Slabs81To120
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 40) :
    StartupPrefix.CellDrift 6 ⟨81 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin6.Slab81.drift_in_mesh
  · exact Cells.Bin6.Slab82.drift_in_mesh
  · exact Cells.Bin6.Slab83.drift_in_mesh
  · exact Cells.Bin6.Slab84.drift_in_mesh
  · exact Cells.Bin6.Slab85.drift_in_mesh
  · exact Cells.Bin6.Slab86.drift_in_mesh
  · exact Cells.Bin6.Slab87.drift_in_mesh
  · exact Cells.Bin6.Slab88.drift_in_mesh
  · exact Cells.Bin6.Slab89.drift_in_mesh
  · exact Cells.Bin6.Slab90.drift_in_mesh
  · exact Cells.Bin6.Slab91.drift_in_mesh
  · exact Cells.Bin6.Slab92.drift_in_mesh
  · exact Cells.Bin6.Slab93.drift_in_mesh
  · exact Cells.Bin6.Slab94.drift_in_mesh
  · exact Cells.Bin6.Slab95.drift_in_mesh
  · exact Cells.Bin6.Slab96.drift_in_mesh
  · exact Cells.Bin6.Slab97.drift_in_mesh
  · exact Cells.Bin6.Slab98.drift_in_mesh
  · exact Cells.Bin6.Slab99.drift_in_mesh
  · exact Cells.Bin6.Slab100.drift_in_mesh
  · exact Cells.Bin6.Slab101.drift_in_mesh
  · exact Cells.Bin6.Slab102.drift_in_mesh
  · exact Cells.Bin6.Slab103.drift_in_mesh
  · exact Cells.Bin6.Slab104.drift_in_mesh
  · exact Cells.Bin6.Slab105.drift_in_mesh
  · exact Cells.Bin6.Slab106.drift_in_mesh
  · exact Cells.Bin6.Slab107.drift_in_mesh
  · exact Cells.Bin6.Slab108.drift_in_mesh
  · exact Cells.Bin6.Slab109.drift_in_mesh
  · exact Cells.Bin6.Slab110.drift_in_mesh
  · exact Cells.Bin6.Slab111.drift_in_mesh
  · exact Cells.Bin6.Slab112.drift_in_mesh
  · exact Cells.Bin6.Slab113.drift_in_mesh
  · exact Cells.Bin6.Slab114.drift_in_mesh
  · exact Cells.Bin6.Slab115.drift_in_mesh
  · exact Cells.Bin6.Slab116.drift_in_mesh
  · exact Cells.Bin6.Slab117.drift_in_mesh
  · exact Cells.Bin6.Slab118.drift_in_mesh
  · exact Cells.Bin6.Slab119.drift_in_mesh
  · exact Cells.Bin6.Slab120.drift_in_mesh

theorem output (i : Fin 40) :
    SafetyComposition.CellOutput 6 ⟨81 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin6.Slab81.shifted_output_in_mesh
  · exact Cells.Bin6.Slab82.shifted_output_in_mesh
  · exact Cells.Bin6.Slab83.shifted_output_in_mesh
  · exact Cells.Bin6.Slab84.shifted_output_in_mesh
  · exact Cells.Bin6.Slab85.shifted_output_in_mesh
  · exact Cells.Bin6.Slab86.shifted_output_in_mesh
  · exact Cells.Bin6.Slab87.shifted_output_in_mesh
  · exact Cells.Bin6.Slab88.shifted_output_in_mesh
  · exact Cells.Bin6.Slab89.shifted_output_in_mesh
  · exact Cells.Bin6.Slab90.shifted_output_in_mesh
  · exact Cells.Bin6.Slab91.shifted_output_in_mesh
  · exact Cells.Bin6.Slab92.shifted_output_in_mesh
  · exact Cells.Bin6.Slab93.shifted_output_in_mesh
  · exact Cells.Bin6.Slab94.shifted_output_in_mesh
  · exact Cells.Bin6.Slab95.shifted_output_in_mesh
  · exact Cells.Bin6.Slab96.shifted_output_in_mesh
  · exact Cells.Bin6.Slab97.shifted_output_in_mesh
  · exact Cells.Bin6.Slab98.shifted_output_in_mesh
  · exact Cells.Bin6.Slab99.shifted_output_in_mesh
  · exact Cells.Bin6.Slab100.shifted_output_in_mesh
  · exact Cells.Bin6.Slab101.shifted_output_in_mesh
  · exact Cells.Bin6.Slab102.shifted_output_in_mesh
  · exact Cells.Bin6.Slab103.shifted_output_in_mesh
  · exact Cells.Bin6.Slab104.shifted_output_in_mesh
  · exact Cells.Bin6.Slab105.shifted_output_in_mesh
  · exact Cells.Bin6.Slab106.shifted_output_in_mesh
  · exact Cells.Bin6.Slab107.shifted_output_in_mesh
  · exact Cells.Bin6.Slab108.shifted_output_in_mesh
  · exact Cells.Bin6.Slab109.shifted_output_in_mesh
  · exact Cells.Bin6.Slab110.shifted_output_in_mesh
  · exact Cells.Bin6.Slab111.shifted_output_in_mesh
  · exact Cells.Bin6.Slab112.shifted_output_in_mesh
  · exact Cells.Bin6.Slab113.shifted_output_in_mesh
  · exact Cells.Bin6.Slab114.shifted_output_in_mesh
  · exact Cells.Bin6.Slab115.shifted_output_in_mesh
  · exact Cells.Bin6.Slab116.shifted_output_in_mesh
  · exact Cells.Bin6.Slab117.shifted_output_in_mesh
  · exact Cells.Bin6.Slab118.shifted_output_in_mesh
  · exact Cells.Bin6.Slab119.shifted_output_in_mesh
  · exact Cells.Bin6.Slab120.shifted_output_in_mesh


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin6Slabs81To120
