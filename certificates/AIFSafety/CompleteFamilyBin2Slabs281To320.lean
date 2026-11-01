import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin2.Slab281
import AIFSafety.Cells.Bin2.Slab282
import AIFSafety.Cells.Bin2.Slab283
import AIFSafety.Cells.Bin2.Slab284
import AIFSafety.Cells.Bin2.Slab285
import AIFSafety.Cells.Bin2.Slab286
import AIFSafety.Cells.Bin2.Slab287
import AIFSafety.Cells.Bin2.Slab288
import AIFSafety.Cells.Bin2.Slab289
import AIFSafety.Cells.Bin2.Slab290
import AIFSafety.Cells.Bin2.Slab291
import AIFSafety.Cells.Bin2.Slab292
import AIFSafety.Cells.Bin2.Slab293
import AIFSafety.Cells.Bin2.Slab294
import AIFSafety.Cells.Bin2.Slab295
import AIFSafety.Cells.Bin2.Slab296
import AIFSafety.Cells.Bin2.Slab297
import AIFSafety.Cells.Bin2.Slab298
import AIFSafety.Cells.Bin2.Slab299
import AIFSafety.Cells.Bin2.Slab300
import AIFSafety.Cells.Bin2.Slab301
import AIFSafety.Cells.Bin2.Slab302
import AIFSafety.Cells.Bin2.Slab303
import AIFSafety.Cells.Bin2.Slab304
import AIFSafety.Cells.Bin2.Slab305
import AIFSafety.Cells.Bin2.Slab306
import AIFSafety.Cells.Bin2.Slab307
import AIFSafety.Cells.Bin2.Slab308
import AIFSafety.Cells.Bin2.Slab309
import AIFSafety.Cells.Bin2.Slab310
import AIFSafety.Cells.Bin2.Slab311
import AIFSafety.Cells.Bin2.Slab312
import AIFSafety.Cells.Bin2.Slab313
import AIFSafety.Cells.Bin2.Slab314
import AIFSafety.Cells.Bin2.Slab315
import AIFSafety.Cells.Bin2.Slab316
import AIFSafety.Cells.Bin2.Slab317
import AIFSafety.Cells.Bin2.Slab318
import AIFSafety.Cells.Bin2.Slab319
import AIFSafety.Cells.Bin2.Slab320

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin2Slabs281To320
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 40) :
    StartupPrefix.CellDrift 2 ⟨281 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin2.Slab281.drift_in_mesh
  · exact Cells.Bin2.Slab282.drift_in_mesh
  · exact Cells.Bin2.Slab283.drift_in_mesh
  · exact Cells.Bin2.Slab284.drift_in_mesh
  · exact Cells.Bin2.Slab285.drift_in_mesh
  · exact Cells.Bin2.Slab286.drift_in_mesh
  · exact Cells.Bin2.Slab287.drift_in_mesh
  · exact Cells.Bin2.Slab288.drift_in_mesh
  · exact Cells.Bin2.Slab289.drift_in_mesh
  · exact Cells.Bin2.Slab290.drift_in_mesh
  · exact Cells.Bin2.Slab291.drift_in_mesh
  · exact Cells.Bin2.Slab292.drift_in_mesh
  · exact Cells.Bin2.Slab293.drift_in_mesh
  · exact Cells.Bin2.Slab294.drift_in_mesh
  · exact Cells.Bin2.Slab295.drift_in_mesh
  · exact Cells.Bin2.Slab296.drift_in_mesh
  · exact Cells.Bin2.Slab297.drift_in_mesh
  · exact Cells.Bin2.Slab298.drift_in_mesh
  · exact Cells.Bin2.Slab299.drift_in_mesh
  · exact Cells.Bin2.Slab300.drift_in_mesh
  · exact Cells.Bin2.Slab301.drift_in_mesh
  · exact Cells.Bin2.Slab302.drift_in_mesh
  · exact Cells.Bin2.Slab303.drift_in_mesh
  · exact Cells.Bin2.Slab304.drift_in_mesh
  · exact Cells.Bin2.Slab305.drift_in_mesh
  · exact Cells.Bin2.Slab306.drift_in_mesh
  · exact Cells.Bin2.Slab307.drift_in_mesh
  · exact Cells.Bin2.Slab308.drift_in_mesh
  · exact Cells.Bin2.Slab309.drift_in_mesh
  · exact Cells.Bin2.Slab310.drift_in_mesh
  · exact Cells.Bin2.Slab311.drift_in_mesh
  · exact Cells.Bin2.Slab312.drift_in_mesh
  · exact Cells.Bin2.Slab313.drift_in_mesh
  · exact Cells.Bin2.Slab314.drift_in_mesh
  · exact Cells.Bin2.Slab315.drift_in_mesh
  · exact Cells.Bin2.Slab316.drift_in_mesh
  · exact Cells.Bin2.Slab317.drift_in_mesh
  · exact Cells.Bin2.Slab318.drift_in_mesh
  · exact Cells.Bin2.Slab319.drift_in_mesh
  · exact Cells.Bin2.Slab320.drift_in_mesh

theorem output (i : Fin 40) :
    SafetyComposition.CellOutput 2 ⟨281 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin2.Slab281.shifted_output_in_mesh
  · exact Cells.Bin2.Slab282.shifted_output_in_mesh
  · exact Cells.Bin2.Slab283.shifted_output_in_mesh
  · exact Cells.Bin2.Slab284.shifted_output_in_mesh
  · exact Cells.Bin2.Slab285.shifted_output_in_mesh
  · exact Cells.Bin2.Slab286.shifted_output_in_mesh
  · exact Cells.Bin2.Slab287.shifted_output_in_mesh
  · exact Cells.Bin2.Slab288.shifted_output_in_mesh
  · exact Cells.Bin2.Slab289.shifted_output_in_mesh
  · exact Cells.Bin2.Slab290.shifted_output_in_mesh
  · exact Cells.Bin2.Slab291.shifted_output_in_mesh
  · exact Cells.Bin2.Slab292.shifted_output_in_mesh
  · exact Cells.Bin2.Slab293.shifted_output_in_mesh
  · exact Cells.Bin2.Slab294.shifted_output_in_mesh
  · exact Cells.Bin2.Slab295.shifted_output_in_mesh
  · exact Cells.Bin2.Slab296.shifted_output_in_mesh
  · exact Cells.Bin2.Slab297.shifted_output_in_mesh
  · exact Cells.Bin2.Slab298.shifted_output_in_mesh
  · exact Cells.Bin2.Slab299.shifted_output_in_mesh
  · exact Cells.Bin2.Slab300.shifted_output_in_mesh
  · exact Cells.Bin2.Slab301.shifted_output_in_mesh
  · exact Cells.Bin2.Slab302.shifted_output_in_mesh
  · exact Cells.Bin2.Slab303.shifted_output_in_mesh
  · exact Cells.Bin2.Slab304.shifted_output_in_mesh
  · exact Cells.Bin2.Slab305.shifted_output_in_mesh
  · exact Cells.Bin2.Slab306.shifted_output_in_mesh
  · exact Cells.Bin2.Slab307.shifted_output_in_mesh
  · exact Cells.Bin2.Slab308.shifted_output_in_mesh
  · exact Cells.Bin2.Slab309.shifted_output_in_mesh
  · exact Cells.Bin2.Slab310.shifted_output_in_mesh
  · exact Cells.Bin2.Slab311.shifted_output_in_mesh
  · exact Cells.Bin2.Slab312.shifted_output_in_mesh
  · exact Cells.Bin2.Slab313.shifted_output_in_mesh
  · exact Cells.Bin2.Slab314.shifted_output_in_mesh
  · exact Cells.Bin2.Slab315.shifted_output_in_mesh
  · exact Cells.Bin2.Slab316.shifted_output_in_mesh
  · exact Cells.Bin2.Slab317.shifted_output_in_mesh
  · exact Cells.Bin2.Slab318.shifted_output_in_mesh
  · exact Cells.Bin2.Slab319.shifted_output_in_mesh
  · exact Cells.Bin2.Slab320.shifted_output_in_mesh


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin2Slabs281To320
