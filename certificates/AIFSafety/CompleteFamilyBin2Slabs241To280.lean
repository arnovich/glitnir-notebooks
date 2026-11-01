import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin2.Slab241
import AIFSafety.Cells.Bin2.Slab242
import AIFSafety.Cells.Bin2.Slab243
import AIFSafety.Cells.Bin2.Slab244
import AIFSafety.Cells.Bin2.Slab245
import AIFSafety.Cells.Bin2.Slab246
import AIFSafety.Cells.Bin2.Slab247
import AIFSafety.Cells.Bin2.Slab248
import AIFSafety.Cells.Bin2.Slab249
import AIFSafety.Cells.Bin2.Slab250
import AIFSafety.Cells.Bin2.Slab251
import AIFSafety.Cells.Bin2.Slab252
import AIFSafety.Cells.Bin2.Slab253
import AIFSafety.Cells.Bin2.Slab254
import AIFSafety.Cells.Bin2.Slab255
import AIFSafety.Cells.Bin2.Slab256
import AIFSafety.Cells.Bin2.Slab257
import AIFSafety.Cells.Bin2.Slab258
import AIFSafety.Cells.Bin2.Slab259
import AIFSafety.Cells.Bin2.Slab260
import AIFSafety.Cells.Bin2.Slab261
import AIFSafety.Cells.Bin2.Slab262
import AIFSafety.Cells.Bin2.Slab263
import AIFSafety.Cells.Bin2.Slab264
import AIFSafety.Cells.Bin2.Slab265
import AIFSafety.Cells.Bin2.Slab266
import AIFSafety.Cells.Bin2.Slab267
import AIFSafety.Cells.Bin2.Slab268
import AIFSafety.Cells.Bin2.Slab269
import AIFSafety.Cells.Bin2.Slab270
import AIFSafety.Cells.Bin2.Slab271
import AIFSafety.Cells.Bin2.Slab272
import AIFSafety.Cells.Bin2.Slab273
import AIFSafety.Cells.Bin2.Slab274
import AIFSafety.Cells.Bin2.Slab275
import AIFSafety.Cells.Bin2.Slab276
import AIFSafety.Cells.Bin2.Slab277
import AIFSafety.Cells.Bin2.Slab278
import AIFSafety.Cells.Bin2.Slab279
import AIFSafety.Cells.Bin2.Slab280

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin2Slabs241To280
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 40) :
    StartupPrefix.CellDrift 2 ⟨241 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin2.Slab241.drift_in_mesh
  · exact Cells.Bin2.Slab242.drift_in_mesh
  · exact Cells.Bin2.Slab243.drift_in_mesh
  · exact Cells.Bin2.Slab244.drift_in_mesh
  · exact Cells.Bin2.Slab245.drift_in_mesh
  · exact Cells.Bin2.Slab246.drift_in_mesh
  · exact Cells.Bin2.Slab247.drift_in_mesh
  · exact Cells.Bin2.Slab248.drift_in_mesh
  · exact Cells.Bin2.Slab249.drift_in_mesh
  · exact Cells.Bin2.Slab250.drift_in_mesh
  · exact Cells.Bin2.Slab251.drift_in_mesh
  · exact Cells.Bin2.Slab252.drift_in_mesh
  · exact Cells.Bin2.Slab253.drift_in_mesh
  · exact Cells.Bin2.Slab254.drift_in_mesh
  · exact Cells.Bin2.Slab255.drift_in_mesh
  · exact Cells.Bin2.Slab256.drift_in_mesh
  · exact Cells.Bin2.Slab257.drift_in_mesh
  · exact Cells.Bin2.Slab258.drift_in_mesh
  · exact Cells.Bin2.Slab259.drift_in_mesh
  · exact Cells.Bin2.Slab260.drift_in_mesh
  · exact Cells.Bin2.Slab261.drift_in_mesh
  · exact Cells.Bin2.Slab262.drift_in_mesh
  · exact Cells.Bin2.Slab263.drift_in_mesh
  · exact Cells.Bin2.Slab264.drift_in_mesh
  · exact Cells.Bin2.Slab265.drift_in_mesh
  · exact Cells.Bin2.Slab266.drift_in_mesh
  · exact Cells.Bin2.Slab267.drift_in_mesh
  · exact Cells.Bin2.Slab268.drift_in_mesh
  · exact Cells.Bin2.Slab269.drift_in_mesh
  · exact Cells.Bin2.Slab270.drift_in_mesh
  · exact Cells.Bin2.Slab271.drift_in_mesh
  · exact Cells.Bin2.Slab272.drift_in_mesh
  · exact Cells.Bin2.Slab273.drift_in_mesh
  · exact Cells.Bin2.Slab274.drift_in_mesh
  · exact Cells.Bin2.Slab275.drift_in_mesh
  · exact Cells.Bin2.Slab276.drift_in_mesh
  · exact Cells.Bin2.Slab277.drift_in_mesh
  · exact Cells.Bin2.Slab278.drift_in_mesh
  · exact Cells.Bin2.Slab279.drift_in_mesh
  · exact Cells.Bin2.Slab280.drift_in_mesh

theorem output (i : Fin 40) :
    SafetyComposition.CellOutput 2 ⟨241 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin2.Slab241.shifted_output_in_mesh
  · exact Cells.Bin2.Slab242.shifted_output_in_mesh
  · exact Cells.Bin2.Slab243.shifted_output_in_mesh
  · exact Cells.Bin2.Slab244.shifted_output_in_mesh
  · exact Cells.Bin2.Slab245.shifted_output_in_mesh
  · exact Cells.Bin2.Slab246.shifted_output_in_mesh
  · exact Cells.Bin2.Slab247.shifted_output_in_mesh
  · exact Cells.Bin2.Slab248.shifted_output_in_mesh
  · exact Cells.Bin2.Slab249.shifted_output_in_mesh
  · exact Cells.Bin2.Slab250.shifted_output_in_mesh
  · exact Cells.Bin2.Slab251.shifted_output_in_mesh
  · exact Cells.Bin2.Slab252.shifted_output_in_mesh
  · exact Cells.Bin2.Slab253.shifted_output_in_mesh
  · exact Cells.Bin2.Slab254.shifted_output_in_mesh
  · exact Cells.Bin2.Slab255.shifted_output_in_mesh
  · exact Cells.Bin2.Slab256.shifted_output_in_mesh
  · exact Cells.Bin2.Slab257.shifted_output_in_mesh
  · exact Cells.Bin2.Slab258.shifted_output_in_mesh
  · exact Cells.Bin2.Slab259.shifted_output_in_mesh
  · exact Cells.Bin2.Slab260.shifted_output_in_mesh
  · exact Cells.Bin2.Slab261.shifted_output_in_mesh
  · exact Cells.Bin2.Slab262.shifted_output_in_mesh
  · exact Cells.Bin2.Slab263.shifted_output_in_mesh
  · exact Cells.Bin2.Slab264.shifted_output_in_mesh
  · exact Cells.Bin2.Slab265.shifted_output_in_mesh
  · exact Cells.Bin2.Slab266.shifted_output_in_mesh
  · exact Cells.Bin2.Slab267.shifted_output_in_mesh
  · exact Cells.Bin2.Slab268.shifted_output_in_mesh
  · exact Cells.Bin2.Slab269.shifted_output_in_mesh
  · exact Cells.Bin2.Slab270.shifted_output_in_mesh
  · exact Cells.Bin2.Slab271.shifted_output_in_mesh
  · exact Cells.Bin2.Slab272.shifted_output_in_mesh
  · exact Cells.Bin2.Slab273.shifted_output_in_mesh
  · exact Cells.Bin2.Slab274.shifted_output_in_mesh
  · exact Cells.Bin2.Slab275.shifted_output_in_mesh
  · exact Cells.Bin2.Slab276.shifted_output_in_mesh
  · exact Cells.Bin2.Slab277.shifted_output_in_mesh
  · exact Cells.Bin2.Slab278.shifted_output_in_mesh
  · exact Cells.Bin2.Slab279.shifted_output_in_mesh
  · exact Cells.Bin2.Slab280.shifted_output_in_mesh


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin2Slabs241To280
