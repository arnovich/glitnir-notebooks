import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin7.Slab21
import AIFSafety.Cells.Bin7.Slab22
import AIFSafety.Cells.Bin7.Slab23
import AIFSafety.Cells.Bin7.Slab24
import AIFSafety.Cells.Bin7.Slab25
import AIFSafety.Cells.Bin7.Slab26
import AIFSafety.Cells.Bin7.Slab27
import AIFSafety.Cells.Bin7.Slab28
import AIFSafety.Cells.Bin7.Slab29
import AIFSafety.Cells.Bin7.Slab30
import AIFSafety.Cells.Bin7.Slab31
import AIFSafety.Cells.Bin7.Slab32
import AIFSafety.Cells.Bin7.Slab33
import AIFSafety.Cells.Bin7.Slab34
import AIFSafety.Cells.Bin7.Slab35
import AIFSafety.Cells.Bin7.Slab36
import AIFSafety.Cells.Bin7.Slab37
import AIFSafety.Cells.Bin7.Slab38
import AIFSafety.Cells.Bin7.Slab39
import AIFSafety.Cells.Bin7.Slab40

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin7Slabs21To40
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 20) :
    StartupPrefix.CellDrift 7 ⟨21 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin7.Slab21.drift_in_mesh
  · exact Cells.Bin7.Slab22.drift_in_mesh
  · exact Cells.Bin7.Slab23.drift_in_mesh
  · exact Cells.Bin7.Slab24.drift_in_mesh
  · exact Cells.Bin7.Slab25.drift_in_mesh
  · exact Cells.Bin7.Slab26.drift_in_mesh
  · exact Cells.Bin7.Slab27.drift_in_mesh
  · exact Cells.Bin7.Slab28.drift_in_mesh
  · exact Cells.Bin7.Slab29.drift_in_mesh
  · exact Cells.Bin7.Slab30.drift_in_mesh
  · exact Cells.Bin7.Slab31.drift_in_mesh
  · exact Cells.Bin7.Slab32.drift_in_mesh
  · exact Cells.Bin7.Slab33.drift_in_mesh
  · exact Cells.Bin7.Slab34.drift_in_mesh
  · exact Cells.Bin7.Slab35.drift_in_mesh
  · exact Cells.Bin7.Slab36.drift_in_mesh
  · exact Cells.Bin7.Slab37.drift_in_mesh
  · exact Cells.Bin7.Slab38.drift_in_mesh
  · exact Cells.Bin7.Slab39.drift_in_mesh
  · exact Cells.Bin7.Slab40.drift_in_mesh

theorem output (i : Fin 20) :
    SafetyComposition.CellOutput 7 ⟨21 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin7.Slab21.shifted_output_in_mesh
  · exact Cells.Bin7.Slab22.shifted_output_in_mesh
  · exact Cells.Bin7.Slab23.shifted_output_in_mesh
  · exact Cells.Bin7.Slab24.shifted_output_in_mesh
  · exact Cells.Bin7.Slab25.shifted_output_in_mesh
  · exact Cells.Bin7.Slab26.shifted_output_in_mesh
  · exact Cells.Bin7.Slab27.shifted_output_in_mesh
  · exact Cells.Bin7.Slab28.shifted_output_in_mesh
  · exact Cells.Bin7.Slab29.shifted_output_in_mesh
  · exact Cells.Bin7.Slab30.shifted_output_in_mesh
  · exact Cells.Bin7.Slab31.shifted_output_in_mesh
  · exact Cells.Bin7.Slab32.shifted_output_in_mesh
  · exact Cells.Bin7.Slab33.shifted_output_in_mesh
  · exact Cells.Bin7.Slab34.shifted_output_in_mesh
  · exact Cells.Bin7.Slab35.shifted_output_in_mesh
  · exact Cells.Bin7.Slab36.shifted_output_in_mesh
  · exact Cells.Bin7.Slab37.shifted_output_in_mesh
  · exact Cells.Bin7.Slab38.shifted_output_in_mesh
  · exact Cells.Bin7.Slab39.shifted_output_in_mesh
  · exact Cells.Bin7.Slab40.shifted_output_in_mesh


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin7Slabs21To40
