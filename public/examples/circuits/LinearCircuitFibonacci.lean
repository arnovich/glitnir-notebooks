import MathlibExt.LinearAlgebra.FiniteObservations
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Two linear systems producing the Fibonacci stream

Compare the simultaneous recurrences

$$ (x_0,x_1)^+ = (x_0+x_1,x_0), \qquad o_x=x_0, $$
$$ (y_0,y_1,y_2)^+ = (y_1,y_0+y_1,2y_2), \qquad o_y=y_1. $$

At starts $(0,1)$ and $(1,0,1)$, both output prefixes are $0,1,1,2,3$.
Observation zero reads the initial state. The extra coordinate doubles and is
unobserved: output agreement does not imply bounded or identical states.

Atlas proves that the first five observations determine agreement forever,
because five is the sum of the dimensions. We apply that theorem to real
matrices, including every real scaling of the stated starts. These are matrix
results; compilation and program Hoare judgments belong to the separate private
circuit examples and are not claims of this notebook.
-/

namespace Notebook.LinearCircuitFibonacci

open scoped Matrix

/-- The two-state Fibonacci transition. -/
def fibonacci : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]

/-- An equivalent output with an additional unobserved doubling coordinate. -/
def extendedFibonacci : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 1, 1, 0; 0, 0, 2]

/-- The visible coordinates, permuted consistently. -/
def permutedFibonacci : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 1]

/-!
## Check five observations {fold}

For starts $(0,r)$ and $(r,0,r)$, check the first five outputs symbolically.
The argument uses exact real arithmetic and makes no assumption about later
observations.
-/

theorem fibonacci_scaled_prefix (r : ℝ) : ∀ n < 2 + 3,
    Matrix.observation fibonacci ![0, r] ![1, 0] n =
      Matrix.observation extendedFibonacci ![r, 0, r] ![0, 1, 0] n := by
  intro n hn
  interval_cases n <;>
    norm_num [Matrix.observation, fibonacci, extendedFibonacci, pow_succ,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-!
## Extend agreement to every step {fold}

Atlas's Cayley–Hamilton argument turns the finite prefix into equality at all
natural-number steps. Specialize the real scale to one for the stated stream.
-/

theorem fibonacci_scaled_equivalent (r : ℝ) : ∀ n,
    Matrix.observation fibonacci ![0, r] ![1, 0] n =
      Matrix.observation extendedFibonacci ![r, 0, r] ![0, 1, 0] n := by
  exact (Matrix.observation_prefix_iff_all _ _ _ _ _ _).mp
    (fibonacci_scaled_prefix r)

theorem fibonacci_equivalent : ∀ n,
    Matrix.observation fibonacci ![0, 1] ![1, 0] n =
      Matrix.observation extendedFibonacci ![1, 0, 1] ![0, 1, 0] n :=
  fibonacci_scaled_equivalent 1

/-!
## Permute the coordinates {fold}

Two states on each side require four comparisons. Swapping both the transition
and the readout consistently preserves the whole output stream.
-/

theorem permutation_prefix : ∀ n < 2 + 2,
    Matrix.observation fibonacci ![0, 1] ![1, 0] n =
      Matrix.observation permutedFibonacci ![1, 0] ![0, 1] n := by
  intro n hn
  interval_cases n <;>
    norm_num [Matrix.observation, fibonacci, permutedFibonacci, pow_succ,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem permutation_equivalent : ∀ n,
    Matrix.observation fibonacci ![0, 1] ![1, 0] n =
      Matrix.observation permutedFibonacci ![1, 0] ![0, 1] n := by
  exact (Matrix.observation_prefix_iff_all _ _ _ _ _ _).mp permutation_prefix

#print axioms fibonacci_scaled_equivalent
#print axioms permutation_equivalent

end Notebook.LinearCircuitFibonacci
