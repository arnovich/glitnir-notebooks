import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin6.Slab1
import AIFSafety.Cells.Bin6.Slab2
import AIFSafety.Cells.Bin6.Slab3
import AIFSafety.Cells.Bin6.Slab4
import AIFSafety.Cells.Bin6.Slab5
import AIFSafety.Cells.Bin6.Slab6
import AIFSafety.Cells.Bin6.Slab7
import AIFSafety.Cells.Bin6.Slab8
import AIFSafety.Cells.Bin6.Slab9
import AIFSafety.Cells.Bin6.Slab10
import AIFSafety.Cells.Bin6.Slab11
import AIFSafety.Cells.Bin6.Slab12
import AIFSafety.Cells.Bin6.Slab13
import AIFSafety.Cells.Bin6.Slab14
import AIFSafety.Cells.Bin6.Slab15
import AIFSafety.Cells.Bin6.Slab16
import AIFSafety.Cells.Bin6.Slab17
import AIFSafety.Cells.Bin6.Slab18
import AIFSafety.Cells.Bin6.Slab19
import AIFSafety.Cells.Bin6.Slab20

/-! All 21 drift and output obligations in parameter bin 6.
Only concrete checked certificates are used; no cell obligation is assumed. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.UniformPrefixBin6
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 21) :
    StartupPrefix.CellDrift 6 ⟨i.val, by omega⟩ := by
  fin_cases i
  · exact StartupPrefix.first_drift 6
  · exact Cells.Bin6.Slab1.drift_in_mesh
  · exact Cells.Bin6.Slab2.drift_in_mesh
  · exact Cells.Bin6.Slab3.drift_in_mesh
  · exact Cells.Bin6.Slab4.drift_in_mesh
  · exact Cells.Bin6.Slab5.drift_in_mesh
  · exact Cells.Bin6.Slab6.drift_in_mesh
  · exact Cells.Bin6.Slab7.drift_in_mesh
  · exact Cells.Bin6.Slab8.drift_in_mesh
  · exact Cells.Bin6.Slab9.drift_in_mesh
  · exact Cells.Bin6.Slab10.drift_in_mesh
  · exact Cells.Bin6.Slab11.drift_in_mesh
  · exact Cells.Bin6.Slab12.drift_in_mesh
  · exact Cells.Bin6.Slab13.drift_in_mesh
  · exact Cells.Bin6.Slab14.drift_in_mesh
  · exact Cells.Bin6.Slab15.drift_in_mesh
  · exact Cells.Bin6.Slab16.drift_in_mesh
  · exact Cells.Bin6.Slab17.drift_in_mesh
  · exact Cells.Bin6.Slab18.drift_in_mesh
  · exact Cells.Bin6.Slab19.drift_in_mesh
  · exact Cells.Bin6.Slab20.drift_in_mesh

theorem output (i : Fin 21) :
    SafetyComposition.CellOutput 6 ⟨i.val, by omega⟩ := by
  fin_cases i
  · exact StartupOutput.first_cell_output 6
  · exact Cells.Bin6.Slab1.shifted_output_in_mesh
  · exact Cells.Bin6.Slab2.shifted_output_in_mesh
  · exact Cells.Bin6.Slab3.shifted_output_in_mesh
  · exact Cells.Bin6.Slab4.shifted_output_in_mesh
  · exact Cells.Bin6.Slab5.shifted_output_in_mesh
  · exact Cells.Bin6.Slab6.shifted_output_in_mesh
  · exact Cells.Bin6.Slab7.shifted_output_in_mesh
  · exact Cells.Bin6.Slab8.shifted_output_in_mesh
  · exact Cells.Bin6.Slab9.shifted_output_in_mesh
  · exact Cells.Bin6.Slab10.shifted_output_in_mesh
  · exact Cells.Bin6.Slab11.shifted_output_in_mesh
  · exact Cells.Bin6.Slab12.shifted_output_in_mesh
  · exact Cells.Bin6.Slab13.shifted_output_in_mesh
  · exact Cells.Bin6.Slab14.shifted_output_in_mesh
  · exact Cells.Bin6.Slab15.shifted_output_in_mesh
  · exact Cells.Bin6.Slab16.shifted_output_in_mesh
  · exact Cells.Bin6.Slab17.shifted_output_in_mesh
  · exact Cells.Bin6.Slab18.shifted_output_in_mesh
  · exact Cells.Bin6.Slab19.shifted_output_in_mesh
  · exact Cells.Bin6.Slab20.shifted_output_in_mesh

#print axioms drift
#print axioms output
end AIFSafety.UniformPrefixBin6
