import Gimle.Forseti.Examples.AIFLocalEntry

/-! Rational evaluation is bound exactly to the already proved real quadratic. -/
namespace AIFSafety.TerminalEnergy
open Gimle.Forseti Gimle.Forseti.Examples
open AIFLocalEntry AIFLocalStability

def rationalValue (x : Fin 4 → ℚ) : ℚ :=
  (11399/50000)*x 0*x 0+(8053/25000)*x 0*x 1+(-6353/50000)*x 0*x 2+
  (19/2500)*x 0*x 3+(32597/100000)*x 1*x 1+(-3073/6250)*x 1*x 2+
  (-19/10000)*x 1*x 3+(19513/50000)*x 2*x 2+(-13/625)*x 2*x 3+
  (5579/100000)*x 3*x 3

theorem rational_binding (x : Fin 4 → ℚ) :
    (rationalValue x : ℝ) = value (fun i => (x i : ℝ)) := by
  simp [rationalValue,value,energy]

theorem real_bound (x : Fin 4 → ℚ) (h : rationalValue x ≤ 1/400) :
    value (fun i => (x i : ℝ)) ≤ 1/400 := by
  rw [← rational_binding]
  have hc : (rationalValue x : ℝ) ≤ ((1/400 : ℚ) : ℝ) := Rat.cast_le.mpr h
  norm_num at hc ⊢
  exact hc

#print axioms rational_binding
#print axioms real_bound
end AIFSafety.TerminalEnergy
