import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin5.Slab201
import AIFSafety.Cells.Bin5.Slab202
import AIFSafety.Cells.Bin5.Slab203
import AIFSafety.Cells.Bin5.Slab204
import AIFSafety.Cells.Bin5.Slab205
import AIFSafety.Cells.Bin5.Slab206
import AIFSafety.Cells.Bin5.Slab207
import AIFSafety.Cells.Bin5.Slab208
import AIFSafety.Cells.Bin5.Slab209
import AIFSafety.Cells.Bin5.Slab210
import AIFSafety.Cells.Bin5.Slab211
import AIFSafety.Cells.Bin5.Slab212
import AIFSafety.Cells.Bin5.Slab213
import AIFSafety.Cells.Bin5.Slab214
import AIFSafety.Cells.Bin5.Slab215
import AIFSafety.Cells.Bin5.Slab216
import AIFSafety.Cells.Bin5.Slab217
import AIFSafety.Cells.Bin5.Slab218
import AIFSafety.Cells.Bin5.Slab219
import AIFSafety.Cells.Bin5.Slab220
import AIFSafety.Cells.Bin5.Slab221
import AIFSafety.Cells.Bin5.Slab222
import AIFSafety.Cells.Bin5.Slab223
import AIFSafety.Cells.Bin5.Slab224
import AIFSafety.Cells.Bin5.Slab225
import AIFSafety.Cells.Bin5.Slab226
import AIFSafety.Cells.Bin5.Slab227
import AIFSafety.Cells.Bin5.Slab228
import AIFSafety.Cells.Bin5.Slab229
import AIFSafety.Cells.Bin5.Slab230
import AIFSafety.Cells.Bin5.Slab231
import AIFSafety.Cells.Bin5.Slab232
import AIFSafety.Cells.Bin5.Slab233
import AIFSafety.Cells.Bin5.Slab234
import AIFSafety.Cells.Bin5.Slab235
import AIFSafety.Cells.Bin5.Slab236
import AIFSafety.Cells.Bin5.Slab237
import AIFSafety.Cells.Bin5.Slab238
import AIFSafety.Cells.Bin5.Slab239
import AIFSafety.Cells.Bin5.Slab240

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin5Slabs201To240
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 40) :
    StartupPrefix.CellDrift 5 ⟨201 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin5.Slab201.drift_in_mesh
  · exact Cells.Bin5.Slab202.drift_in_mesh
  · exact Cells.Bin5.Slab203.drift_in_mesh
  · exact Cells.Bin5.Slab204.drift_in_mesh
  · exact Cells.Bin5.Slab205.drift_in_mesh
  · exact Cells.Bin5.Slab206.drift_in_mesh
  · exact Cells.Bin5.Slab207.drift_in_mesh
  · exact Cells.Bin5.Slab208.drift_in_mesh
  · exact Cells.Bin5.Slab209.drift_in_mesh
  · exact Cells.Bin5.Slab210.drift_in_mesh
  · exact Cells.Bin5.Slab211.drift_in_mesh
  · exact Cells.Bin5.Slab212.drift_in_mesh
  · exact Cells.Bin5.Slab213.drift_in_mesh
  · exact Cells.Bin5.Slab214.drift_in_mesh
  · exact Cells.Bin5.Slab215.drift_in_mesh
  · exact Cells.Bin5.Slab216.drift_in_mesh
  · exact Cells.Bin5.Slab217.drift_in_mesh
  · exact Cells.Bin5.Slab218.drift_in_mesh
  · exact Cells.Bin5.Slab219.drift_in_mesh
  · exact Cells.Bin5.Slab220.drift_in_mesh
  · exact Cells.Bin5.Slab221.drift_in_mesh
  · exact Cells.Bin5.Slab222.drift_in_mesh
  · exact Cells.Bin5.Slab223.drift_in_mesh
  · exact Cells.Bin5.Slab224.drift_in_mesh
  · exact Cells.Bin5.Slab225.drift_in_mesh
  · exact Cells.Bin5.Slab226.drift_in_mesh
  · exact Cells.Bin5.Slab227.drift_in_mesh
  · exact Cells.Bin5.Slab228.drift_in_mesh
  · exact Cells.Bin5.Slab229.drift_in_mesh
  · exact Cells.Bin5.Slab230.drift_in_mesh
  · exact Cells.Bin5.Slab231.drift_in_mesh
  · exact Cells.Bin5.Slab232.drift_in_mesh
  · exact Cells.Bin5.Slab233.drift_in_mesh
  · exact Cells.Bin5.Slab234.drift_in_mesh
  · exact Cells.Bin5.Slab235.drift_in_mesh
  · exact Cells.Bin5.Slab236.drift_in_mesh
  · exact Cells.Bin5.Slab237.drift_in_mesh
  · exact Cells.Bin5.Slab238.drift_in_mesh
  · exact Cells.Bin5.Slab239.drift_in_mesh
  · exact Cells.Bin5.Slab240.drift_in_mesh

theorem output (i : Fin 40) :
    SafetyComposition.CellOutput 5 ⟨201 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin5.Slab201.shifted_output_in_mesh
  · exact Cells.Bin5.Slab202.shifted_output_in_mesh
  · exact Cells.Bin5.Slab203.shifted_output_in_mesh
  · exact Cells.Bin5.Slab204.shifted_output_in_mesh
  · exact Cells.Bin5.Slab205.shifted_output_in_mesh
  · exact Cells.Bin5.Slab206.shifted_output_in_mesh
  · exact Cells.Bin5.Slab207.shifted_output_in_mesh
  · exact Cells.Bin5.Slab208.shifted_output_in_mesh
  · exact Cells.Bin5.Slab209.shifted_output_in_mesh
  · exact Cells.Bin5.Slab210.shifted_output_in_mesh
  · exact Cells.Bin5.Slab211.shifted_output_in_mesh
  · exact Cells.Bin5.Slab212.shifted_output_in_mesh
  · exact Cells.Bin5.Slab213.shifted_output_in_mesh
  · exact Cells.Bin5.Slab214.shifted_output_in_mesh
  · exact Cells.Bin5.Slab215.shifted_output_in_mesh
  · exact Cells.Bin5.Slab216.shifted_output_in_mesh
  · exact Cells.Bin5.Slab217.shifted_output_in_mesh
  · exact Cells.Bin5.Slab218.shifted_output_in_mesh
  · exact Cells.Bin5.Slab219.shifted_output_in_mesh
  · exact Cells.Bin5.Slab220.shifted_output_in_mesh
  · exact Cells.Bin5.Slab221.shifted_output_in_mesh
  · exact Cells.Bin5.Slab222.shifted_output_in_mesh
  · exact Cells.Bin5.Slab223.shifted_output_in_mesh
  · exact Cells.Bin5.Slab224.shifted_output_in_mesh
  · exact Cells.Bin5.Slab225.shifted_output_in_mesh
  · exact Cells.Bin5.Slab226.shifted_output_in_mesh
  · exact Cells.Bin5.Slab227.shifted_output_in_mesh
  · exact Cells.Bin5.Slab228.shifted_output_in_mesh
  · exact Cells.Bin5.Slab229.shifted_output_in_mesh
  · exact Cells.Bin5.Slab230.shifted_output_in_mesh
  · exact Cells.Bin5.Slab231.shifted_output_in_mesh
  · exact Cells.Bin5.Slab232.shifted_output_in_mesh
  · exact Cells.Bin5.Slab233.shifted_output_in_mesh
  · exact Cells.Bin5.Slab234.shifted_output_in_mesh
  · exact Cells.Bin5.Slab235.shifted_output_in_mesh
  · exact Cells.Bin5.Slab236.shifted_output_in_mesh
  · exact Cells.Bin5.Slab237.shifted_output_in_mesh
  · exact Cells.Bin5.Slab238.shifted_output_in_mesh
  · exact Cells.Bin5.Slab239.shifted_output_in_mesh
  · exact Cells.Bin5.Slab240.shifted_output_in_mesh


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin5Slabs201To240
