import AIFSafety.CompleteFamilyBin0
import AIFSafety.CompleteFamilyBin1
import AIFSafety.CompleteFamilyBin2
import AIFSafety.CompleteFamilyBin3
import AIFSafety.CompleteFamilyBin4
import AIFSafety.CompleteFamilyBin5
import AIFSafety.CompleteFamilyBin6
import AIFSafety.CompleteFamilyBin7

/-! Every cell of the mesh: the drift and output certificates of all 8 × 370
cells, collected from the per-bin modules. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamily
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (b : Fin 8) (i : Fin 370) : StartupPrefix.CellDrift b i := by
  fin_cases b
  · exact CompleteFamilyBin0.drift i
  · exact CompleteFamilyBin1.drift i
  · exact CompleteFamilyBin2.drift i
  · exact CompleteFamilyBin3.drift i
  · exact CompleteFamilyBin4.drift i
  · exact CompleteFamilyBin5.drift i
  · exact CompleteFamilyBin6.drift i
  · exact CompleteFamilyBin7.drift i

theorem output (b : Fin 8) (i : Fin 370) : SafetyComposition.CellOutput b i := by
  fin_cases b
  · exact CompleteFamilyBin0.output i
  · exact CompleteFamilyBin1.output i
  · exact CompleteFamilyBin2.output i
  · exact CompleteFamilyBin3.output i
  · exact CompleteFamilyBin4.output i
  · exact CompleteFamilyBin5.output i
  · exact CompleteFamilyBin6.output i
  · exact CompleteFamilyBin7.output i


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamily
