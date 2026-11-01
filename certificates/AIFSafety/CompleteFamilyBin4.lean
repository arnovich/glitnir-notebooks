import AIFSafety.UniformPrefix
import AIFSafety.CompleteFamilyBin4Slabs21To40
import AIFSafety.CompleteFamilyBin4Slabs41To80
import AIFSafety.CompleteFamilyBin4Slabs81To120
import AIFSafety.CompleteFamilyBin4Slabs121To160
import AIFSafety.CompleteFamilyBin4Slabs161To200
import AIFSafety.CompleteFamilyBin4Slabs201To240
import AIFSafety.CompleteFamilyBin4Slabs241To280
import AIFSafety.CompleteFamilyBin4Slabs281To320
import AIFSafety.CompleteFamilyBin4Slabs321To360
import AIFSafety.CompleteFamilyBin4Slabs361To369

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace AIFSafety.CompleteFamilyBin4
open Gimle.Forseti Gimle.Forseti.Examples

theorem drift (i : Fin 370) : StartupPrefix.CellDrift 4 i := by
  by_cases h0 : i.val < 21
  · exact UniformPrefix.drift 4 ⟨i.val, h0⟩
  by_cases h1 : i.val < 41
  · let j : Fin 20 := ⟨i.val - 21, by omega⟩
    have checked := CompleteFamilyBin4Slabs21To40.drift j
    have index_eq : (⟨21 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change StartupPrefix.CellDrift 4 (⟨21 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h2 : i.val < 81
  · let j : Fin 40 := ⟨i.val - 41, by omega⟩
    have checked := CompleteFamilyBin4Slabs41To80.drift j
    have index_eq : (⟨41 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change StartupPrefix.CellDrift 4 (⟨41 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h3 : i.val < 121
  · let j : Fin 40 := ⟨i.val - 81, by omega⟩
    have checked := CompleteFamilyBin4Slabs81To120.drift j
    have index_eq : (⟨81 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change StartupPrefix.CellDrift 4 (⟨81 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h4 : i.val < 161
  · let j : Fin 40 := ⟨i.val - 121, by omega⟩
    have checked := CompleteFamilyBin4Slabs121To160.drift j
    have index_eq : (⟨121 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change StartupPrefix.CellDrift 4 (⟨121 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h5 : i.val < 201
  · let j : Fin 40 := ⟨i.val - 161, by omega⟩
    have checked := CompleteFamilyBin4Slabs161To200.drift j
    have index_eq : (⟨161 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change StartupPrefix.CellDrift 4 (⟨161 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h6 : i.val < 241
  · let j : Fin 40 := ⟨i.val - 201, by omega⟩
    have checked := CompleteFamilyBin4Slabs201To240.drift j
    have index_eq : (⟨201 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change StartupPrefix.CellDrift 4 (⟨201 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h7 : i.val < 281
  · let j : Fin 40 := ⟨i.val - 241, by omega⟩
    have checked := CompleteFamilyBin4Slabs241To280.drift j
    have index_eq : (⟨241 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change StartupPrefix.CellDrift 4 (⟨241 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h8 : i.val < 321
  · let j : Fin 40 := ⟨i.val - 281, by omega⟩
    have checked := CompleteFamilyBin4Slabs281To320.drift j
    have index_eq : (⟨281 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change StartupPrefix.CellDrift 4 (⟨281 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h9 : i.val < 361
  · let j : Fin 40 := ⟨i.val - 321, by omega⟩
    have checked := CompleteFamilyBin4Slabs321To360.drift j
    have index_eq : (⟨321 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change StartupPrefix.CellDrift 4 (⟨321 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  let j : Fin 9 := ⟨i.val - 361, by omega⟩
  have checked := CompleteFamilyBin4Slabs361To369.drift j
  have index_eq : (⟨361 + j.val, by omega⟩ : Fin 370) = i := by
    apply Fin.ext
    dsimp [j]
    omega
  change StartupPrefix.CellDrift 4 (⟨361 + j.val, by omega⟩ : Fin 370) at checked
  rw [index_eq] at checked
  exact checked

theorem output (i : Fin 370) : SafetyComposition.CellOutput 4 i := by
  by_cases h0 : i.val < 21
  · exact UniformPrefix.output 4 ⟨i.val, h0⟩
  by_cases h1 : i.val < 41
  · let j : Fin 20 := ⟨i.val - 21, by omega⟩
    have checked := CompleteFamilyBin4Slabs21To40.output j
    have index_eq : (⟨21 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change SafetyComposition.CellOutput 4 (⟨21 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h2 : i.val < 81
  · let j : Fin 40 := ⟨i.val - 41, by omega⟩
    have checked := CompleteFamilyBin4Slabs41To80.output j
    have index_eq : (⟨41 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change SafetyComposition.CellOutput 4 (⟨41 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h3 : i.val < 121
  · let j : Fin 40 := ⟨i.val - 81, by omega⟩
    have checked := CompleteFamilyBin4Slabs81To120.output j
    have index_eq : (⟨81 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change SafetyComposition.CellOutput 4 (⟨81 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h4 : i.val < 161
  · let j : Fin 40 := ⟨i.val - 121, by omega⟩
    have checked := CompleteFamilyBin4Slabs121To160.output j
    have index_eq : (⟨121 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change SafetyComposition.CellOutput 4 (⟨121 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h5 : i.val < 201
  · let j : Fin 40 := ⟨i.val - 161, by omega⟩
    have checked := CompleteFamilyBin4Slabs161To200.output j
    have index_eq : (⟨161 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change SafetyComposition.CellOutput 4 (⟨161 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h6 : i.val < 241
  · let j : Fin 40 := ⟨i.val - 201, by omega⟩
    have checked := CompleteFamilyBin4Slabs201To240.output j
    have index_eq : (⟨201 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change SafetyComposition.CellOutput 4 (⟨201 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h7 : i.val < 281
  · let j : Fin 40 := ⟨i.val - 241, by omega⟩
    have checked := CompleteFamilyBin4Slabs241To280.output j
    have index_eq : (⟨241 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change SafetyComposition.CellOutput 4 (⟨241 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h8 : i.val < 321
  · let j : Fin 40 := ⟨i.val - 281, by omega⟩
    have checked := CompleteFamilyBin4Slabs281To320.output j
    have index_eq : (⟨281 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change SafetyComposition.CellOutput 4 (⟨281 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  by_cases h9 : i.val < 361
  · let j : Fin 40 := ⟨i.val - 321, by omega⟩
    have checked := CompleteFamilyBin4Slabs321To360.output j
    have index_eq : (⟨321 + j.val, by omega⟩ : Fin 370) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    change SafetyComposition.CellOutput 4 (⟨321 + j.val, by omega⟩ : Fin 370) at checked
    rw [index_eq] at checked
    exact checked
  let j : Fin 9 := ⟨i.val - 361, by omega⟩
  have checked := CompleteFamilyBin4Slabs361To369.output j
  have index_eq : (⟨361 + j.val, by omega⟩ : Fin 370) = i := by
    apply Fin.ext
    dsimp [j]
    omega
  change SafetyComposition.CellOutput 4 (⟨361 + j.val, by omega⟩ : Fin 370) at checked
  rw [index_eq] at checked
  exact checked

#print axioms drift
#print axioms output
end AIFSafety.CompleteFamilyBin4
