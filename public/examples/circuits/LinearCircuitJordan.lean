import MathlibExt.LinearAlgebra.FiniteObservations
import Mathlib.Tactic.FinCases

/-!
# Equivalent damped Jordan chains

Two linear systems can move through different states and still produce the
same output stream. Damped Jordan chains show this in its simplest form: the
two systems below differ in how strongly each coordinate feeds the next, yet a
suitably scaled readout of the last coordinate is the same at every step.

Let $S$ be the nilpotent shift, which moves every coordinate one place down and
inserts a zero; in dimension three it sends $(x_0,x_1,x_2)$ to $(0,x_0,x_1)$.
Compare the updates

$$ A = \tfrac12(I + S), \qquad B = \tfrac12 I + S. $$

Both start at the first basis vector $e_0$. Read the last coordinate of the
first system and one quarter of the last coordinate of the second:

$$ o_A(n) = (A^n e_0)_2, \qquad o_B(n) = \tfrac14\,(B^n e_0)_2. $$

After one step the middle coordinates already differ, $\tfrac12$ against $1$,
yet the two output streams agree. Expanding the binomials gives
$o_A(n) = o_B(n) = \binom{n}{2}\,2^{-n}$, so the outputs start
$0, 0, \tfrac14, \tfrac38, \tfrac38, \tfrac5{16}$. That expansion is ours, not
Lean's: the claims below check the equality for every $n$, and the first six
values of $o_A$ exactly.

Six comparisons suffice because the sum of the dimensions is six. We also check
the one- and two-dimensional versions, with output scalings $1$ and $\tfrac12$.
These are exact rational matrix calculations. They do not claim compilation
correctness or a program Hoare judgment; those remain in the private circuit
examples.
The proved property is output equality; a decay-rate or stability estimate
would require a separate theorem.
-/
namespace Notebook.LinearCircuitJordan

open scoped Matrix

/-- The transition $A = (I + S)/2$ in dimension 1. -/
def jordanLeft1 : Matrix (Fin 1) (Fin 1) ℚ := !![1 / 2]

/-- The transition $B = I/2 + S$ in dimension 1. -/
def jordanRight1 : Matrix (Fin 1) (Fin 1) ℚ := !![1 / 2]

/-- The first basis vector. -/
def initial1 : Fin 1 → ℚ := ![1]

/-- The transition $A = (I + S)/2$ in dimension 2. -/
def jordanLeft2 : Matrix (Fin 2) (Fin 2) ℚ := !![1 / 2, 0; 1 / 2, 1 / 2]

/-- The transition $B = I/2 + S$ in dimension 2. -/
def jordanRight2 : Matrix (Fin 2) (Fin 2) ℚ := !![1 / 2, 0; 1, 1 / 2]

/-- The first basis vector. -/
def initial2 : Fin 2 → ℚ := ![1, 0]

/-- The transition $A = (I + S)/2$ in dimension 3. -/
def jordanLeft3 : Matrix (Fin 3) (Fin 3) ℚ := !![1 / 2, 0, 0; 1 / 2, 1 / 2, 0; 0, 1 / 2, 1 / 2]

/-- The transition $B = I/2 + S$ in dimension 3. -/
def jordanRight3 : Matrix (Fin 3) (Fin 3) ℚ := !![1 / 2, 0, 0; 1, 1 / 2, 0; 0, 1, 1 / 2]

/-- The first basis vector. -/
def initial3 : Fin 3 → ℚ := ![1, 0, 0]

/-!
## Finite prefixes determine the complete streams {fold}

Each finite prefix is checked by exact rational computation. Atlas then uses
Cayley–Hamilton to extend agreement to every natural-number observation.
Dimension one checks the boundary case where the transitions coincide.
-/

/-- The first 2 observations agree. -/
theorem jordan1_prefix : ∀ n : Fin 2,
    Matrix.observation jordanLeft1 initial1 ![1] n =
      Matrix.observation jordanRight1 initial1 ![1] n := by
  decide +kernel

/-- Equality of the entire output streams, by the Atlas dimension bound. -/
theorem jordan1_equivalent : ∀ n : ℕ,
    Matrix.observation jordanLeft1 initial1 ![1] n =
      Matrix.observation jordanRight1 initial1 ![1] n := by
  apply (Matrix.observation_prefix_iff_all _ _ _ _ _ _).mp
  intro n hn
  exact jordan1_prefix ⟨n, hn⟩

/-- The first 4 observations agree. -/
theorem jordan2_prefix : ∀ n : Fin 4,
    Matrix.observation jordanLeft2 initial2 ![0, 1] n =
      Matrix.observation jordanRight2 initial2 ![0, 1 / 2] n := by
  decide +kernel

/-- Equality of the entire output streams, by the Atlas dimension bound. -/
theorem jordan2_equivalent : ∀ n : ℕ,
    Matrix.observation jordanLeft2 initial2 ![0, 1] n =
      Matrix.observation jordanRight2 initial2 ![0, 1 / 2] n := by
  apply (Matrix.observation_prefix_iff_all _ _ _ _ _ _).mp
  intro n hn
  exact jordan2_prefix ⟨n, hn⟩

/-- The first 6 observations agree. -/
theorem jordan3_prefix : ∀ n : Fin 6,
    Matrix.observation jordanLeft3 initial3 ![0, 0, 1] n =
      Matrix.observation jordanRight3 initial3 ![0, 0, 1 / 4] n := by
  decide +kernel

/-- Equality of the entire output streams, by the Atlas dimension bound. -/
theorem jordan3_equivalent : ∀ n : ℕ,
    Matrix.observation jordanLeft3 initial3 ![0, 0, 1] n =
      Matrix.observation jordanRight3 initial3 ![0, 0, 1 / 4] n := by
  apply (Matrix.observation_prefix_iff_all _ _ _ _ _ _).mp
  intro n hn
  exact jordan3_prefix ⟨n, hn⟩

/-!
## Independent numerical controls {fold}

Comparing two realizations alone would not exclude a shared mistake. We also
check the prescribed exact prefixes and unequal next-state coordinates.
-/

/-- The left stream has the stated exact prefix. -/
theorem jordan2_expected : ∀ n : Fin 4,
    Matrix.observation jordanLeft2 initial2 ![0, 1] n =
      (![0, 1 / 2, 1 / 2, 3 / 8] : Fin 4 → ℚ) n := by
  decide +kernel

/-- The middle coordinate differs after one update. -/
theorem jordan2_different_updates :
    jordanLeft2.mulVec initial2 1 ≠ jordanRight2.mulVec initial2 1 := by
  decide +kernel

/-- The left stream has the stated exact prefix. -/
theorem jordan3_expected : ∀ n : Fin 6,
    Matrix.observation jordanLeft3 initial3 ![0, 0, 1] n =
      (![0, 0, 1 / 4, 3 / 8, 3 / 8, 5 / 16] : Fin 6 → ℚ) n := by
  decide +kernel

/-- The middle coordinate differs after one update. -/
theorem jordan3_different_updates :
    jordanLeft3.mulVec initial3 1 ≠ jordanRight3.mulVec initial3 1 := by
  decide +kernel

#print axioms jordan1_equivalent
#print axioms jordan2_equivalent
#print axioms jordan3_equivalent

end Notebook.LinearCircuitJordan
