import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Does a damped scalar stay in its band?

One state $x$, damped at a constant rate:

$$ x' = -k x $$

with $k = \tfrac12$, started from $x = 1$ at time $t = 0$. We watch the energy
$V = x^2$, which starts at $1$.

There is no coupling here and nothing driving the system, so the damping is the
only thing that moves $V$. Because $k$ is positive, the energy should never
grow. This notebook turns that intuition into claims Lean checks, and marks
where it is left open.

The same question for three coupled states, where the coupling makes the
argument less direct, is taken up in [ThreeState](ThreeState.lean).

## What is modelled, and what is not

The questions are about the exact real solution for $t \ge 0$, for this one
rate and this one initial state. The claims below are facts about every state
$x$; carrying them over to the solution is an argument made in the prose, not a
claim. They say nothing about other starts, other rates, or a discretized
implementation. No simulation enters any claim's
status.
-/

namespace Notebook.ScalarDecay

/-- The damping rate. -/
noncomputable def k : ℝ := 1 / 2

/-- The rate is positive, which is what makes the system a damped one. -/
theorem k_pos : 0 < k := by
  unfold k
  norm_num

/-!
## The energy never grows

The energy is $V = x^2$, so along a solution its rate is $V' = 2xx' = 2x(-kx)$.
Write that out and it is $-2kx^2$, which is a negative multiple of a square.
This is the whole decay argument, stated for every state the system could be in
rather than for the particular trajectory.
-/

/-- The energy rate is never positive, at any state. -/
theorem energy_rate_nonpositive (x : ℝ) : 2 * x * (-k * x) ≤ 0 := by
  have hk : 0 < k := k_pos
  nlinarith [sq_nonneg x]

/-!
## The energy stays in its band

The band has two sides, and only one of them needs the dynamics. The upper side
follows from the claim above: the energy starts at $1$ and its rate is never
positive, so it never climbs past $1$. That last step integrates the rate along
the solution; it is ours, not Lean's. The lower side needs nothing at all about this system,
because an energy is a square.

That asymmetry is worth stating rather than hiding: a reader should be able to
see which half of $[0, 1]$ is earned by the damping argument and which half is
free.
-/

/-- The energy is never negative, whatever the state. -/
theorem energy_nonneg (x : ℝ) : 0 ≤ x ^ 2 := by
  exact sq_nonneg x

/-!
## Does the energy stay above a floor?

The intuition says no: the damping drives $x$ towards zero, so the energy falls
below any positive floor eventually. The claim below asserts the opposite, over
every state rather than just the start, which makes it plainly false — $x = 0$
refutes it. It is left unproved on purpose, so the notebook shows an open status
beside the checked ones.

Note what the status does *not* say. `open` means no proof has been checked, not
that the claim is false; Glitnir would only report it refuted once a proof of its
negation had itself been checked.
-/

/-- The energy never falls below a quarter. Unproved, and in fact false. -/
theorem energy_above_floor (x : ℝ) : (1 : ℝ) / 4 ≤ x ^ 2 := by
  sorry

end Notebook.ScalarDecay
