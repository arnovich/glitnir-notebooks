import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin7.Slab121
import AIFSafety.Cells.Bin7.Slab122
import AIFSafety.Cells.Bin7.Slab123
import AIFSafety.Cells.Bin7.Slab124
import AIFSafety.Cells.Bin7.Slab125
import AIFSafety.Cells.Bin7.Slab126
import AIFSafety.Cells.Bin7.Slab127
import AIFSafety.Cells.Bin7.Slab128
import AIFSafety.Cells.Bin7.Slab129
import AIFSafety.Cells.Bin7.Slab130
import AIFSafety.Cells.Bin7.Slab131
import AIFSafety.Cells.Bin7.Slab132
import AIFSafety.Cells.Bin7.Slab133
import AIFSafety.Cells.Bin7.Slab134
import AIFSafety.Cells.Bin7.Slab135
import AIFSafety.Cells.Bin7.Slab136
import AIFSafety.Cells.Bin7.Slab137
import AIFSafety.Cells.Bin7.Slab138
import AIFSafety.Cells.Bin7.Slab139
import AIFSafety.Cells.Bin7.Slab140
import AIFSafety.Cells.Bin7.Slab141
import AIFSafety.Cells.Bin7.Slab142
import AIFSafety.Cells.Bin7.Slab143
import AIFSafety.Cells.Bin7.Slab144
import AIFSafety.Cells.Bin7.Slab145
import AIFSafety.Cells.Bin7.Slab146
import AIFSafety.Cells.Bin7.Slab147
import AIFSafety.Cells.Bin7.Slab148
import AIFSafety.Cells.Bin7.Slab149
import AIFSafety.Cells.Bin7.Slab150
import AIFSafety.Cells.Bin7.Slab151
import AIFSafety.Cells.Bin7.Slab152
import AIFSafety.Cells.Bin7.Slab153
import AIFSafety.Cells.Bin7.Slab154
import AIFSafety.Cells.Bin7.Slab155
import AIFSafety.Cells.Bin7.Slab156
import AIFSafety.Cells.Bin7.Slab157
import AIFSafety.Cells.Bin7.Slab158
import AIFSafety.Cells.Bin7.Slab159
import AIFSafety.Cells.Bin7.Slab160

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin7Slabs121To160
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 40) :
    StartupPrefix.CellDrift 7 ⟨121 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin7.Slab121.drift_in_mesh
  · exact Cells.Bin7.Slab122.drift_in_mesh
  · exact Cells.Bin7.Slab123.drift_in_mesh
  · exact Cells.Bin7.Slab124.drift_in_mesh
  · exact Cells.Bin7.Slab125.drift_in_mesh
  · exact Cells.Bin7.Slab126.drift_in_mesh
  · exact Cells.Bin7.Slab127.drift_in_mesh
  · exact Cells.Bin7.Slab128.drift_in_mesh
  · exact Cells.Bin7.Slab129.drift_in_mesh
  · exact Cells.Bin7.Slab130.drift_in_mesh
  · exact Cells.Bin7.Slab131.drift_in_mesh
  · exact Cells.Bin7.Slab132.drift_in_mesh
  · exact Cells.Bin7.Slab133.drift_in_mesh
  · exact Cells.Bin7.Slab134.drift_in_mesh
  · exact Cells.Bin7.Slab135.drift_in_mesh
  · exact Cells.Bin7.Slab136.drift_in_mesh
  · exact Cells.Bin7.Slab137.drift_in_mesh
  · exact Cells.Bin7.Slab138.drift_in_mesh
  · exact Cells.Bin7.Slab139.drift_in_mesh
  · exact Cells.Bin7.Slab140.drift_in_mesh
  · exact Cells.Bin7.Slab141.drift_in_mesh
  · exact Cells.Bin7.Slab142.drift_in_mesh
  · exact Cells.Bin7.Slab143.drift_in_mesh
  · exact Cells.Bin7.Slab144.drift_in_mesh
  · exact Cells.Bin7.Slab145.drift_in_mesh
  · exact Cells.Bin7.Slab146.drift_in_mesh
  · exact Cells.Bin7.Slab147.drift_in_mesh
  · exact Cells.Bin7.Slab148.drift_in_mesh
  · exact Cells.Bin7.Slab149.drift_in_mesh
  · exact Cells.Bin7.Slab150.drift_in_mesh
  · exact Cells.Bin7.Slab151.drift_in_mesh
  · exact Cells.Bin7.Slab152.drift_in_mesh
  · exact Cells.Bin7.Slab153.drift_in_mesh
  · exact Cells.Bin7.Slab154.drift_in_mesh
  · exact Cells.Bin7.Slab155.drift_in_mesh
  · exact Cells.Bin7.Slab156.drift_in_mesh
  · exact Cells.Bin7.Slab157.drift_in_mesh
  · exact Cells.Bin7.Slab158.drift_in_mesh
  · exact Cells.Bin7.Slab159.drift_in_mesh
  · exact Cells.Bin7.Slab160.drift_in_mesh

theorem output (i : Fin 40) :
    SafetyComposition.CellOutput 7 ⟨121 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin7.Slab121.shifted_output_in_mesh
  · exact Cells.Bin7.Slab122.shifted_output_in_mesh
  · exact Cells.Bin7.Slab123.shifted_output_in_mesh
  · exact Cells.Bin7.Slab124.shifted_output_in_mesh
  · exact Cells.Bin7.Slab125.shifted_output_in_mesh
  · exact Cells.Bin7.Slab126.shifted_output_in_mesh
  · exact Cells.Bin7.Slab127.shifted_output_in_mesh
  · exact Cells.Bin7.Slab128.shifted_output_in_mesh
  · exact Cells.Bin7.Slab129.shifted_output_in_mesh
  · exact Cells.Bin7.Slab130.shifted_output_in_mesh
  · exact Cells.Bin7.Slab131.shifted_output_in_mesh
  · exact Cells.Bin7.Slab132.shifted_output_in_mesh
  · exact Cells.Bin7.Slab133.shifted_output_in_mesh
  · exact Cells.Bin7.Slab134.shifted_output_in_mesh
  · exact Cells.Bin7.Slab135.shifted_output_in_mesh
  · exact Cells.Bin7.Slab136.shifted_output_in_mesh
  · exact Cells.Bin7.Slab137.shifted_output_in_mesh
  · exact Cells.Bin7.Slab138.shifted_output_in_mesh
  · exact Cells.Bin7.Slab139.shifted_output_in_mesh
  · exact Cells.Bin7.Slab140.shifted_output_in_mesh
  · exact Cells.Bin7.Slab141.shifted_output_in_mesh
  · exact Cells.Bin7.Slab142.shifted_output_in_mesh
  · exact Cells.Bin7.Slab143.shifted_output_in_mesh
  · exact Cells.Bin7.Slab144.shifted_output_in_mesh
  · exact Cells.Bin7.Slab145.shifted_output_in_mesh
  · exact Cells.Bin7.Slab146.shifted_output_in_mesh
  · exact Cells.Bin7.Slab147.shifted_output_in_mesh
  · exact Cells.Bin7.Slab148.shifted_output_in_mesh
  · exact Cells.Bin7.Slab149.shifted_output_in_mesh
  · exact Cells.Bin7.Slab150.shifted_output_in_mesh
  · exact Cells.Bin7.Slab151.shifted_output_in_mesh
  · exact Cells.Bin7.Slab152.shifted_output_in_mesh
  · exact Cells.Bin7.Slab153.shifted_output_in_mesh
  · exact Cells.Bin7.Slab154.shifted_output_in_mesh
  · exact Cells.Bin7.Slab155.shifted_output_in_mesh
  · exact Cells.Bin7.Slab156.shifted_output_in_mesh
  · exact Cells.Bin7.Slab157.shifted_output_in_mesh
  · exact Cells.Bin7.Slab158.shifted_output_in_mesh
  · exact Cells.Bin7.Slab159.shifted_output_in_mesh
  · exact Cells.Bin7.Slab160.shifted_output_in_mesh


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin7Slabs121To160
