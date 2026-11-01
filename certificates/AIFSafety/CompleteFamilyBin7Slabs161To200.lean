import AIFSafety.SafetyComposition
import AIFSafety.Cells.Bin7.Slab161
import AIFSafety.Cells.Bin7.Slab162
import AIFSafety.Cells.Bin7.Slab163
import AIFSafety.Cells.Bin7.Slab164
import AIFSafety.Cells.Bin7.Slab165
import AIFSafety.Cells.Bin7.Slab166
import AIFSafety.Cells.Bin7.Slab167
import AIFSafety.Cells.Bin7.Slab168
import AIFSafety.Cells.Bin7.Slab169
import AIFSafety.Cells.Bin7.Slab170
import AIFSafety.Cells.Bin7.Slab171
import AIFSafety.Cells.Bin7.Slab172
import AIFSafety.Cells.Bin7.Slab173
import AIFSafety.Cells.Bin7.Slab174
import AIFSafety.Cells.Bin7.Slab175
import AIFSafety.Cells.Bin7.Slab176
import AIFSafety.Cells.Bin7.Slab177
import AIFSafety.Cells.Bin7.Slab178
import AIFSafety.Cells.Bin7.Slab179
import AIFSafety.Cells.Bin7.Slab180
import AIFSafety.Cells.Bin7.Slab181
import AIFSafety.Cells.Bin7.Slab182
import AIFSafety.Cells.Bin7.Slab183
import AIFSafety.Cells.Bin7.Slab184
import AIFSafety.Cells.Bin7.Slab185
import AIFSafety.Cells.Bin7.Slab186
import AIFSafety.Cells.Bin7.Slab187
import AIFSafety.Cells.Bin7.Slab188
import AIFSafety.Cells.Bin7.Slab189
import AIFSafety.Cells.Bin7.Slab190
import AIFSafety.Cells.Bin7.Slab191
import AIFSafety.Cells.Bin7.Slab192
import AIFSafety.Cells.Bin7.Slab193
import AIFSafety.Cells.Bin7.Slab194
import AIFSafety.Cells.Bin7.Slab195
import AIFSafety.Cells.Bin7.Slab196
import AIFSafety.Cells.Bin7.Slab197
import AIFSafety.Cells.Bin7.Slab198
import AIFSafety.Cells.Bin7.Slab199
import AIFSafety.Cells.Bin7.Slab200

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin7Slabs161To200
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 40) :
    StartupPrefix.CellDrift 7 ⟨161 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin7.Slab161.drift_in_mesh
  · exact Cells.Bin7.Slab162.drift_in_mesh
  · exact Cells.Bin7.Slab163.drift_in_mesh
  · exact Cells.Bin7.Slab164.drift_in_mesh
  · exact Cells.Bin7.Slab165.drift_in_mesh
  · exact Cells.Bin7.Slab166.drift_in_mesh
  · exact Cells.Bin7.Slab167.drift_in_mesh
  · exact Cells.Bin7.Slab168.drift_in_mesh
  · exact Cells.Bin7.Slab169.drift_in_mesh
  · exact Cells.Bin7.Slab170.drift_in_mesh
  · exact Cells.Bin7.Slab171.drift_in_mesh
  · exact Cells.Bin7.Slab172.drift_in_mesh
  · exact Cells.Bin7.Slab173.drift_in_mesh
  · exact Cells.Bin7.Slab174.drift_in_mesh
  · exact Cells.Bin7.Slab175.drift_in_mesh
  · exact Cells.Bin7.Slab176.drift_in_mesh
  · exact Cells.Bin7.Slab177.drift_in_mesh
  · exact Cells.Bin7.Slab178.drift_in_mesh
  · exact Cells.Bin7.Slab179.drift_in_mesh
  · exact Cells.Bin7.Slab180.drift_in_mesh
  · exact Cells.Bin7.Slab181.drift_in_mesh
  · exact Cells.Bin7.Slab182.drift_in_mesh
  · exact Cells.Bin7.Slab183.drift_in_mesh
  · exact Cells.Bin7.Slab184.drift_in_mesh
  · exact Cells.Bin7.Slab185.drift_in_mesh
  · exact Cells.Bin7.Slab186.drift_in_mesh
  · exact Cells.Bin7.Slab187.drift_in_mesh
  · exact Cells.Bin7.Slab188.drift_in_mesh
  · exact Cells.Bin7.Slab189.drift_in_mesh
  · exact Cells.Bin7.Slab190.drift_in_mesh
  · exact Cells.Bin7.Slab191.drift_in_mesh
  · exact Cells.Bin7.Slab192.drift_in_mesh
  · exact Cells.Bin7.Slab193.drift_in_mesh
  · exact Cells.Bin7.Slab194.drift_in_mesh
  · exact Cells.Bin7.Slab195.drift_in_mesh
  · exact Cells.Bin7.Slab196.drift_in_mesh
  · exact Cells.Bin7.Slab197.drift_in_mesh
  · exact Cells.Bin7.Slab198.drift_in_mesh
  · exact Cells.Bin7.Slab199.drift_in_mesh
  · exact Cells.Bin7.Slab200.drift_in_mesh

theorem output (i : Fin 40) :
    SafetyComposition.CellOutput 7 ⟨161 + i.val, by omega⟩ := by
  fin_cases i
  · exact Cells.Bin7.Slab161.shifted_output_in_mesh
  · exact Cells.Bin7.Slab162.shifted_output_in_mesh
  · exact Cells.Bin7.Slab163.shifted_output_in_mesh
  · exact Cells.Bin7.Slab164.shifted_output_in_mesh
  · exact Cells.Bin7.Slab165.shifted_output_in_mesh
  · exact Cells.Bin7.Slab166.shifted_output_in_mesh
  · exact Cells.Bin7.Slab167.shifted_output_in_mesh
  · exact Cells.Bin7.Slab168.shifted_output_in_mesh
  · exact Cells.Bin7.Slab169.shifted_output_in_mesh
  · exact Cells.Bin7.Slab170.shifted_output_in_mesh
  · exact Cells.Bin7.Slab171.shifted_output_in_mesh
  · exact Cells.Bin7.Slab172.shifted_output_in_mesh
  · exact Cells.Bin7.Slab173.shifted_output_in_mesh
  · exact Cells.Bin7.Slab174.shifted_output_in_mesh
  · exact Cells.Bin7.Slab175.shifted_output_in_mesh
  · exact Cells.Bin7.Slab176.shifted_output_in_mesh
  · exact Cells.Bin7.Slab177.shifted_output_in_mesh
  · exact Cells.Bin7.Slab178.shifted_output_in_mesh
  · exact Cells.Bin7.Slab179.shifted_output_in_mesh
  · exact Cells.Bin7.Slab180.shifted_output_in_mesh
  · exact Cells.Bin7.Slab181.shifted_output_in_mesh
  · exact Cells.Bin7.Slab182.shifted_output_in_mesh
  · exact Cells.Bin7.Slab183.shifted_output_in_mesh
  · exact Cells.Bin7.Slab184.shifted_output_in_mesh
  · exact Cells.Bin7.Slab185.shifted_output_in_mesh
  · exact Cells.Bin7.Slab186.shifted_output_in_mesh
  · exact Cells.Bin7.Slab187.shifted_output_in_mesh
  · exact Cells.Bin7.Slab188.shifted_output_in_mesh
  · exact Cells.Bin7.Slab189.shifted_output_in_mesh
  · exact Cells.Bin7.Slab190.shifted_output_in_mesh
  · exact Cells.Bin7.Slab191.shifted_output_in_mesh
  · exact Cells.Bin7.Slab192.shifted_output_in_mesh
  · exact Cells.Bin7.Slab193.shifted_output_in_mesh
  · exact Cells.Bin7.Slab194.shifted_output_in_mesh
  · exact Cells.Bin7.Slab195.shifted_output_in_mesh
  · exact Cells.Bin7.Slab196.shifted_output_in_mesh
  · exact Cells.Bin7.Slab197.shifted_output_in_mesh
  · exact Cells.Bin7.Slab198.shifted_output_in_mesh
  · exact Cells.Bin7.Slab199.shifted_output_in_mesh
  · exact Cells.Bin7.Slab200.shifted_output_in_mesh


#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin7Slabs161To200
