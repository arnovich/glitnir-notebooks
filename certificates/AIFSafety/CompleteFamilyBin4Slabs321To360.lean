import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin4.Slab321
import AIFSafety.Cells.Bin4.Slab322
import AIFSafety.Cells.Bin4.Slab323
import AIFSafety.Cells.Bin4.Slab324
import AIFSafety.Cells.Bin4.Slab325
import AIFSafety.Cells.Bin4.Slab326
import AIFSafety.Cells.Bin4.Slab327
import AIFSafety.Cells.Bin4.Slab328
import AIFSafety.Cells.Bin4.Slab329
import AIFSafety.Cells.Bin4.Slab330
import AIFSafety.Cells.Bin4.Slab331
import AIFSafety.Cells.Bin4.Slab332
import AIFSafety.Cells.Bin4.Slab333
import AIFSafety.Cells.Bin4.Slab334
import AIFSafety.Cells.Bin4.Slab335
import AIFSafety.Cells.Bin4.Slab336
import AIFSafety.Cells.Bin4.Slab337
import AIFSafety.Cells.Bin4.Slab338
import AIFSafety.Cells.Bin4.Slab339
import AIFSafety.Cells.Bin4.Slab340
import AIFSafety.Cells.Bin4.Slab341
import AIFSafety.Cells.Bin4.Slab342
import AIFSafety.Cells.Bin4.Slab343
import AIFSafety.Cells.Bin4.Slab344
import AIFSafety.Cells.Bin4.Slab345
import AIFSafety.Cells.Bin4.Slab346
import AIFSafety.Cells.Bin4.Slab347
import AIFSafety.Cells.Bin4.Slab348
import AIFSafety.Cells.Bin4.Slab349
import AIFSafety.Cells.Bin4.Slab350
import AIFSafety.Cells.Bin4.Slab351
import AIFSafety.Cells.Bin4.Slab352
import AIFSafety.Cells.Bin4.Slab353
import AIFSafety.Cells.Bin4.Slab354
import AIFSafety.Cells.Bin4.Slab355
import AIFSafety.Cells.Bin4.Slab356
import AIFSafety.Cells.Bin4.Slab357
import AIFSafety.Cells.Bin4.Slab358
import AIFSafety.Cells.Bin4.Slab359
import AIFSafety.Cells.Bin4.Slab360

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin4Slabs321To360
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 40) :
    StartupPrefix.CellDrift 4 ⟨321 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin4.Slab321.drift_in_mesh
  · exact Cells.Bin4.Slab322.drift_in_mesh
  · exact Cells.Bin4.Slab323.drift_in_mesh
  · exact Cells.Bin4.Slab324.drift_in_mesh
  · exact Cells.Bin4.Slab325.drift_in_mesh
  · exact Cells.Bin4.Slab326.drift_in_mesh
  · exact Cells.Bin4.Slab327.drift_in_mesh
  · exact Cells.Bin4.Slab328.drift_in_mesh
  · exact Cells.Bin4.Slab329.drift_in_mesh
  · exact Cells.Bin4.Slab330.drift_in_mesh
  · exact Cells.Bin4.Slab331.drift_in_mesh
  · exact Cells.Bin4.Slab332.drift_in_mesh
  · exact Cells.Bin4.Slab333.drift_in_mesh
  · exact Cells.Bin4.Slab334.drift_in_mesh
  · exact Cells.Bin4.Slab335.drift_in_mesh
  · exact Cells.Bin4.Slab336.drift_in_mesh
  · exact Cells.Bin4.Slab337.drift_in_mesh
  · exact Cells.Bin4.Slab338.drift_in_mesh
  · exact Cells.Bin4.Slab339.drift_in_mesh
  · exact Cells.Bin4.Slab340.drift_in_mesh
  · exact Cells.Bin4.Slab341.drift_in_mesh
  · exact Cells.Bin4.Slab342.drift_in_mesh
  · exact Cells.Bin4.Slab343.drift_in_mesh
  · exact Cells.Bin4.Slab344.drift_in_mesh
  · exact Cells.Bin4.Slab345.drift_in_mesh
  · exact Cells.Bin4.Slab346.drift_in_mesh
  · exact Cells.Bin4.Slab347.drift_in_mesh
  · exact Cells.Bin4.Slab348.drift_in_mesh
  · exact Cells.Bin4.Slab349.drift_in_mesh
  · exact Cells.Bin4.Slab350.drift_in_mesh
  · exact Cells.Bin4.Slab351.drift_in_mesh
  · exact Cells.Bin4.Slab352.drift_in_mesh
  · exact Cells.Bin4.Slab353.drift_in_mesh
  · exact Cells.Bin4.Slab354.drift_in_mesh
  · exact Cells.Bin4.Slab355.drift_in_mesh
  · exact Cells.Bin4.Slab356.drift_in_mesh
  · exact Cells.Bin4.Slab357.drift_in_mesh
  · exact Cells.Bin4.Slab358.drift_in_mesh
  · exact Cells.Bin4.Slab359.drift_in_mesh
  · exact Cells.Bin4.Slab360.drift_in_mesh

theorem output (i : Fin 40) :
    SafetyComposition.CellOutput 4 ⟨321 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin4.Slab321.shifted_output_in_mesh
  · exact Cells.Bin4.Slab322.shifted_output_in_mesh
  · exact Cells.Bin4.Slab323.shifted_output_in_mesh
  · exact Cells.Bin4.Slab324.shifted_output_in_mesh
  · exact Cells.Bin4.Slab325.shifted_output_in_mesh
  · exact Cells.Bin4.Slab326.shifted_output_in_mesh
  · exact Cells.Bin4.Slab327.shifted_output_in_mesh
  · exact Cells.Bin4.Slab328.shifted_output_in_mesh
  · exact Cells.Bin4.Slab329.shifted_output_in_mesh
  · exact Cells.Bin4.Slab330.shifted_output_in_mesh
  · exact Cells.Bin4.Slab331.shifted_output_in_mesh
  · exact Cells.Bin4.Slab332.shifted_output_in_mesh
  · exact Cells.Bin4.Slab333.shifted_output_in_mesh
  · exact Cells.Bin4.Slab334.shifted_output_in_mesh
  · exact Cells.Bin4.Slab335.shifted_output_in_mesh
  · exact Cells.Bin4.Slab336.shifted_output_in_mesh
  · exact Cells.Bin4.Slab337.shifted_output_in_mesh
  · exact Cells.Bin4.Slab338.shifted_output_in_mesh
  · exact Cells.Bin4.Slab339.shifted_output_in_mesh
  · exact Cells.Bin4.Slab340.shifted_output_in_mesh
  · exact Cells.Bin4.Slab341.shifted_output_in_mesh
  · exact Cells.Bin4.Slab342.shifted_output_in_mesh
  · exact Cells.Bin4.Slab343.shifted_output_in_mesh
  · exact Cells.Bin4.Slab344.shifted_output_in_mesh
  · exact Cells.Bin4.Slab345.shifted_output_in_mesh
  · exact Cells.Bin4.Slab346.shifted_output_in_mesh
  · exact Cells.Bin4.Slab347.shifted_output_in_mesh
  · exact Cells.Bin4.Slab348.shifted_output_in_mesh
  · exact Cells.Bin4.Slab349.shifted_output_in_mesh
  · exact Cells.Bin4.Slab350.shifted_output_in_mesh
  · exact Cells.Bin4.Slab351.shifted_output_in_mesh
  · exact Cells.Bin4.Slab352.shifted_output_in_mesh
  · exact Cells.Bin4.Slab353.shifted_output_in_mesh
  · exact Cells.Bin4.Slab354.shifted_output_in_mesh
  · exact Cells.Bin4.Slab355.shifted_output_in_mesh
  · exact Cells.Bin4.Slab356.shifted_output_in_mesh
  · exact Cells.Bin4.Slab357.shifted_output_in_mesh
  · exact Cells.Bin4.Slab358.shifted_output_in_mesh
  · exact Cells.Bin4.Slab359.shifted_output_in_mesh
  · exact Cells.Bin4.Slab360.shifted_output_in_mesh


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin4Slabs321To360
