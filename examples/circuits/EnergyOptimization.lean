import Mathlib
import Gimle.Forseti.Syntax.Certificate
import Gimle.Forseti.Examples.EnergyOptimization

/-!
# Does the safety proof survive the rewrite?

Every change to a circuit breaks its proof. A cheaper implementation, a
compiler pass, a rewrite: the circuit changes, and the safety argument written
for the old one no longer applies to the new one, so someone proves it again,
or nobody does. This notebook shows the argument coming along instead: a
replacement circuit is proposed, Lean checks that it computes exactly the same
function, and the safety contract re-attaches by one rule of the calculus, with
no new proof about the new circuit. It also shows a wrong replacement being
caught.

The circuit computes the energy of a two-dimensional signal,

$$ E(x, y) = (x + y)^2 + (x - y)^2, $$

and comes with a contract: whenever both inputs lie in $[-1, 1]$, the output
lies in $[0, 4]$. The proposed replacement is $2(x^2 + y^2)$, with fewer
arithmetic blocks. Here it was written by hand; a rewrite engine, a search or a
model could have proposed it, and nothing below would change, because the
proposer is never trusted. Lean proves the two circuits equivalent, and only
that proof carries the contract across.

**Proved.** The original circuit meets its contract on $[-1, 1]^2$, with the
bound decided by the entailment decider and its certificate kept for replay.
The replacement computes the same function on every real input, so it meets
the same contract, by one rule. No bound below $4$ holds.

**Refuted.** A tighter bound of $3$. A replacement that multiplies by $3$
instead of $2$: not equivalent, and it breaks the contract at $(1, 1)$.

**Not claimed.** Anything about floating-point evaluation, about inputs outside
the square, or about rewrites in general: the rule is general, the example is
one circuit.

Why this matters: certification is paid per artefact, and every optimisation
produces a new artefact. Here the cost of re-certifying the cheaper circuit is
one equivalence proof, machine-checked, and the rule that transfers the
contract, `exactCircuitSubstitution`, is general within the calculus: any
exact contract carries across any proved equivalence.

Both circuits were written in Python Asgard's combinator language and exported
(`Gimle.Forseti.EnergyDemoData` and `Gimle.Forseti.EnergyOptimizationData`); the
pinned library checks by `rfl` that the definitions used here are those
exports, so every claim below is about the exported circuits. The library also
proves each of these claims itself (`equivalence`, `optimizedBound`,
`wrongViolatesBound`, `upperBoundIsSharp`); they are restated here so that this
notebook's own check, not the library's build, is what carries them.

## Establish the original contract {fold}

The original circuit computes $2x^2 + 2y^2$, which lies in $[0,4]$ on
$[-1,1]^2$. The polynomial certificate gives the circuit's safety contract;
the tighter bound $3$ is refuted.

The circuit duplicates its inputs, forms $x + y$ and $x - y$, squares both and
adds. Lean draws it from the definition:
-/
namespace Notebook.EnergyOptimization
open Gimle.Asgard Gimle.Forseti Gimle.Forseti.EnergyDemo Gimle.Forseti.EnergyOptimization

-- @view circuit Gimle.Asgard.EnergyDemo.energy

/-!
### Identify the computed function {fold}

Expanding the squares, the cross terms cancel and $E(x, y) = 2x^2 + 2y^2$. Lean
checks this by running the circuit symbolically, unfolding every block and
normalising the polynomial.
-/

/-- The exported circuit computes $2x^2 + 2y^2$: the cross terms cancel. -/
theorem energy_formula (input : Point 2) :
    energy.run input 0 = 2 * (input 0)^2 + 2 * (input 1)^2 := by
  norm_num [energy, duplicate, interleave, sumAndDifference, difference, squareBoth, square]
  ring

/-!
### Certify the polynomial bound {fold}

On $[-1,1]^2$, the output lies in $[0,4]$. Lean checks the exact polynomial
certificate produced by the entailment decider.

The contract is a polynomial entailment: from the input bounds
$-1 \le x \le 1$ and $-1 \le y \le 1$, the output bound $0 \le 2x^2 + 2y^2 \le 4$
follows. The entailment decider first searches for a counterexample and,
finding none, for a certificate: an exact identity writing each gap as a sum
of squares plus the hypotheses times sums of squares, which Lean re-checks by
computation. The certificate is kept beside the notebook, and the checker
replays it without Z3.
-/

-- @decide energy_in_band : entailment x, y : x >= -1 and x <= 1 and y >= -1 and y <= 1 |- 2*x^2 + 2*y^2 >= 0 and 2*x^2 + 2*y^2 <= 4

namespace Decided_energy_in_band

def forsetiContext : Gimle.Forseti.Syntax.Context :=
  ⟨["x", "y"], by decide, by decide, by decide⟩

def forsetiAntecedent : Gimle.Forseti.Syntax.Formula 2 :=
  (.and (.and (.and (.atom .ge (.add (.var ⟨0, by decide⟩) (.neg (.neg (.constant (mkRat (1) 1)))))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1)))))) (.atom .ge (.add (.var ⟨1, by decide⟩) (.neg (.neg (.constant (mkRat (1) 1))))))) (.atom .le (.add (.var ⟨1, by decide⟩) (.neg (.constant (mkRat (1) 1))))))

def forsetiConsequent : Gimle.Forseti.Syntax.Formula 2 :=
  (.and (.atom .ge (.add (.mul (.constant (mkRat (2) 1)) (.mul (.var ⟨0, by decide⟩) (.var ⟨0, by decide⟩))) (.mul (.constant (mkRat (2) 1)) (.mul (.var ⟨1, by decide⟩) (.var ⟨1, by decide⟩))))) (.atom .le (.add (.add (.mul (.constant (mkRat (2) 1)) (.mul (.var ⟨0, by decide⟩) (.var ⟨0, by decide⟩))) (.mul (.constant (mkRat (2) 1)) (.mul (.var ⟨1, by decide⟩) (.var ⟨1, by decide⟩)))) (.neg (.constant (mkRat (4) 1))))))

def forsetiGoal : Gimle.Forseti.Syntax.Goal := ⟨forsetiContext, forsetiAntecedent, forsetiConsequent⟩

/-- x, y are real numbers. The entailment decider proved it. Goal (entailment): entailment x, y : x >= -1 and x <= 1 and y >= -1 and y <= 1 |- 2*(x*x) + 2*(y*y) >= 0 and 2*(x*x) + 2*(y*y) <= 4 -/
theorem energy_in_band :
    ∀ x y : ℝ,
      x ≥ -1 ∧ x ≤ 1 ∧ y ≥ -1 ∧ y ≤ 1 →
      2 * (x * x) + 2 * (y * y) ≥ 0 ∧ 2 * (x * x) + 2 * (y * y) ≤ 4 := by
  have root : Gimle.Forseti.Syntax.FormulaEntailment forsetiAntecedent forsetiConsequent := by
    exact Gimle.Forseti.Syntax.EntailmentCertificate.sound forsetiGoal ⟨[⟨⟨[((mkRat (2) 1), (.var ⟨0, by decide⟩)), ((mkRat (2) 1), (.var ⟨1, by decide⟩))]⟩, [⟨[]⟩, ⟨[]⟩, ⟨[]⟩, ⟨[]⟩]⟩, ⟨⟨[]⟩, [⟨[((mkRat (1) 1), (.add (.constant (mkRat (1) 1)) (.neg (.var ⟨0, by decide⟩))))]⟩, ⟨[((mkRat (1) 1), (.add (.constant (mkRat (1) 1)) (.var ⟨0, by decide⟩)))]⟩, ⟨[((mkRat (1) 1), (.add (.constant (mkRat (1) 1)) (.neg (.var ⟨1, by decide⟩))))]⟩, ⟨[((mkRat (1) 1), (.add (.constant (mkRat (1) 1)) (.var ⟨1, by decide⟩)))]⟩]⟩]⟩ (by decide +kernel)
  have forsetiSucc : ∀ {n : Nat} (k : Nat) (h : k + 1 < n + 1), (⟨k + 1, h⟩ : Fin (n + 1)) = Fin.succ ⟨k, Nat.lt_of_succ_lt_succ h⟩ := fun _ _ => rfl
  have forsetiCast0 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (2) 1) : ℚ) : ℝ) = 2 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (4) 1) : ℚ) : ℝ) = 4 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ Gimle.Forseti.Syntax.FormulaEntailment forsetiAntecedent forsetiConsequent) => bridge.mpr root) ?_
  constructor
  · intro claim
    revert claim
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Syntax.FormulaEntailment, forsetiAntecedent, forsetiConsequent, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, forsetiSucc, Fin.cons_succ, Fin.zero_eta, Fin.cons_zero, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc, imp_self]
  · intro lane
    revert lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Syntax.FormulaEntailment, forsetiAntecedent, forsetiConsequent, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, forsetiSucc, Fin.cons_succ, Fin.zero_eta, Fin.cons_zero, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc, imp_self]

end Decided_energy_in_band


/-!
### Test the tighter bound of three {fold}

The bound $3$ is false on the same square. The recorded result checks a
counterexample; the positive claim below deliberately remains unproved.

Could the bound be tighter? Asking for $2x^2 + 2y^2 \le 3$ on the same square
is refuted: the decider produces a point where the claim fails, and Lean checks
that the point satisfies the hypotheses and violates the conclusion, which
proves the negation. The claim below is stated with `sorry` in place of a
proof: it is false, so it has none. That positive theorem remains admitted
and displays **Contains sorry**. The separate theorem
`energy_below_three_refuted` below proves its negation and is checked.
-/

-- @decide energy_below_three : entailment x, y : x >= -1 and x <= 1 and y >= -1 and y <= 1 |- 2*x^2 + 2*y^2 <= 3

namespace Decided_energy_below_three

def forsetiContext : Gimle.Forseti.Syntax.Context :=
  ⟨["x", "y"], by decide, by decide, by decide⟩

def forsetiAntecedent : Gimle.Forseti.Syntax.Formula 2 :=
  (.and (.and (.and (.atom .ge (.add (.var ⟨0, by decide⟩) (.neg (.neg (.constant (mkRat (1) 1)))))) (.atom .le (.add (.var ⟨0, by decide⟩) (.neg (.constant (mkRat (1) 1)))))) (.atom .ge (.add (.var ⟨1, by decide⟩) (.neg (.neg (.constant (mkRat (1) 1))))))) (.atom .le (.add (.var ⟨1, by decide⟩) (.neg (.constant (mkRat (1) 1))))))

def forsetiConsequent : Gimle.Forseti.Syntax.Formula 2 :=
  (.atom .le (.add (.add (.mul (.constant (mkRat (2) 1)) (.mul (.var ⟨0, by decide⟩) (.var ⟨0, by decide⟩))) (.mul (.constant (mkRat (2) 1)) (.mul (.var ⟨1, by decide⟩) (.var ⟨1, by decide⟩)))) (.neg (.constant (mkRat (3) 1)))))

def forsetiGoal : Gimle.Forseti.Syntax.Goal := ⟨forsetiContext, forsetiAntecedent, forsetiConsequent⟩

/-- x, y are real numbers. The entailment decider refuted it. Goal (entailment): entailment x, y : x >= -1 and x <= 1 and y >= -1 and y <= 1 |- 2*(x*x) + 2*(y*y) <= 3 -/
theorem energy_below_three :
    ∀ x y : ℝ, x ≥ -1 ∧ x ≤ 1 ∧ y ≥ -1 ∧ y ≤ 1 → 2 * (x * x) + 2 * (y * y) ≤ 3 := by
  sorry

theorem energy_below_three_refuted : ¬ (∀ x y : ℝ, x ≥ -1 ∧ x ≤ 1 ∧ y ≥ -1 ∧ y ≤ 1 → 2 * (x * x) + 2 * (y * y) ≤ 3) := by
  have refuted : ¬ Gimle.Forseti.Syntax.FormulaEntailment forsetiAntecedent forsetiConsequent := by
    exact Gimle.Forseti.Syntax.refutes_sound forsetiGoal [("x", (mkRat (-3) 4)), ("y", (mkRat (-31) 32))] (by decide +kernel)
  intro claim
  have forsetiSucc : ∀ {n : Nat} (k : Nat) (h : k + 1 < n + 1), (⟨k + 1, h⟩ : Fin (n + 1)) = Fin.succ ⟨k, Nat.lt_of_succ_lt_succ h⟩ := fun _ _ => rfl
  have forsetiCast0 : (((mkRat (1) 1) : ℚ) : ℝ) = 1 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast1 : (((mkRat (2) 1) : ℚ) : ℝ) = 2 := by norm_num [Rat.mkRat_eq_div]
  have forsetiCast2 : (((mkRat (3) 1) : ℚ) : ℝ) = 3 := by norm_num [Rat.mkRat_eq_div]
  refine (fun (bridge : _ ↔ Gimle.Forseti.Syntax.FormulaEntailment forsetiAntecedent forsetiConsequent) => refuted (bridge.mp claim)) ?_
  constructor
  · intro claim
    revert claim
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Syntax.FormulaEntailment, forsetiAntecedent, forsetiConsequent, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, forsetiSucc, Fin.cons_succ, Fin.zero_eta, Fin.cons_zero, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc, imp_self]
  · intro lane
    revert lane
    set_option linter.unusedSimpArgs false in simp only [Gimle.Forseti.Syntax.FormulaEntailment, forsetiAntecedent, forsetiConsequent, Gimle.Forseti.Syntax.Formula.holds, Gimle.Forseti.Syntax.Relation.holds, Gimle.Asgard.Polynomial.Expr.eval, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, forsetiSucc, Fin.cons_succ, Fin.zero_eta, Fin.cons_zero, forsetiCast0, forsetiCast1, forsetiCast2, ← sub_eq_add_neg, sub_zero, sub_nonpos, sub_neg, sub_eq_zero, sub_nonneg, sub_pos, ge_iff_le, gt_iff_lt, and_assoc, or_assoc, imp_self]

end Decided_energy_below_three


/-!
### Attach the bound to the circuit {fold}

Combine the circuit's computed formula with the certified polynomial bound
to obtain its Hoare contract on $[-1,1]^2$.

The decided claims are about the polynomial. The contract is about the circuit:
a precondition on its inputs and a postcondition on its output, what the
calculus calls a Hoare triple. It follows from the formula above and the
decided bound, so the decider's certificate is what carries it.
-/

/-- The contract as a Hoare triple over the exported circuit: inputs in $[-1, 1]^2$ give an output in $[0, 4]$. -/
theorem original_contract :
    ExactHoare EnergyDemoData.precondition energy EnergyDemoData.postcondition := by
  intro input hypothesis
  have bounds : input 0 ≥ -1 ∧ input 0 ≤ 1 ∧ input 1 ≥ -1 ∧ input 1 ≤ 1 := by
    simpa [EnergyDemoData.precondition, and_assoc, and_left_comm, and_comm] using hypothesis
  have band := Decided_energy_in_band.energy_in_band (input 0) (input 1) bounds
  simp only [EnergyDemoData.postcondition, energy_formula, sq]
  constructor <;> linarith [band.1, band.2]

/-!
## Transfer the contract to the replacement {fold}

The replacement computes the same function for every real input. Substituting
that equivalence into the original contract gives the same safety guarantee
on $[-1,1]^2$.

### Check the replacement's equivalence {fold}

The proposed replacement squares each input, adds, and doubles: six blocks
where the original needs fourteen, four of them arithmetic where the original
needs six.
-/

-- @view circuit Gimle.Asgard.EnergyOptimization.optimized

/-- The replacement computes the same function as the original on every real input. -/
theorem same_function : GlobalCircuitEquivalence energy optimized := by
  intro input
  funext coordinate
  have zero : coordinate = 0 := Subsingleton.elim _ _
  subst zero
  rw [energy_formula, optimizedIdentity]
  ring

/-!
### Transfer the contract by substitution {fold}

Equivalence is exactly what the calculus needs: an exact Hoare triple is a
statement about a circuit's function, so it transfers to any circuit with the
same function. The proof is one rule application, substituting the equivalent
circuit into the contract.
-/

/-- The contract transfers to the replacement by substituting the equivalent circuit; nothing new is proved about it. -/
theorem optimised_contract :
    ExactHoare EnergyDemoData.precondition optimized EnergyDemoData.postcondition := by
  exact exactCircuitSubstitution original_contract same_function

/-!
## Check failure cases and sharpness {fold}

Multiplying by $3$ instead of $2$ breaks both equivalence and the safety
contract at $(1,1)$. The correct circuit attains $4$ there, so its uniform
upper bound on the square cannot be lowered.

### Reject the wrong replacement {fold}

At $(1,1)$ the original gives $4$ and the wrong replacement gives $6$.
These differing outputs refute equivalence and violate the original contract.

Suppose the replacement had multiplied by three. The circuit looks just as
plausible, and a proposer that got the constant wrong would not know:
-/

-- @view circuit Gimle.Asgard.EnergyOptimization.wrongMultiplier

/-- At the corner $(1, 1)$ the original circuit gives $4$ and the wrong one gives $6$. -/
theorem wrong_differs :
    energy.run ![1, 1] 0 = 4 ∧ wrongMultiplier.run ![1, 1] 0 = 6 := by
  norm_num [energy_formula, wrongMultiplier, squareBoth, square]

/-- One differing input is enough: the wrong replacement is not equivalent to the original. -/
theorem wrong_not_equivalent : ¬ GlobalCircuitEquivalence energy wrongMultiplier := by
  intro claim
  have equal := congrFun (claim ![1, 1]) 0
  rw [wrong_differs.1, wrong_differs.2] at equal
  norm_num at equal

/-- And it breaks the contract: $(1, 1)$ satisfies the precondition and $6 > 4$. -/
theorem wrong_breaks_contract :
    ¬ ExactHoare EnergyDemoData.precondition wrongMultiplier EnergyDemoData.postcondition := by
  intro claim
  have corner : EnergyDemoData.precondition.holds ![1, 1] := by
    norm_num [EnergyDemoData.precondition]
  have bound := claim ![1, 1] corner
  norm_num [EnergyDemoData.postcondition, wrong_differs.2] at bound

/-!
### Show that four is sharp {fold}

The refuted claim `energy_below_three` says $3$ fails at some point. This says
more: no bound below $4$ works, because the corner attains $4$.
-/

/-- No uniform bound below $4$ holds on the square: the corner $(1, 1)$ attains $4$. -/
theorem four_is_sharp (bound : ℝ)
    (valid : ∀ input, EnergyDemoData.precondition.holds input → energy.run input 0 ≤ bound) :
    4 ≤ bound := by
  have corner : EnergyDemoData.precondition.holds ![1, 1] := by
    norm_num [EnergyDemoData.precondition]
  have at_corner := valid ![1, 1] corner
  rw [wrong_differs.1] at at_corner
  exact at_corner

/-!
## What is claimed, and what is not

Every claim is about the exported circuits over exact real arithmetic: the
equivalence holds for every real input, and the contract for every input in
the square. Nothing here says anything about floating-point evaluation of
either circuit, or about inputs outside the square. The replacement was
checked, not trusted; a replacement that is not an equivalence, like the one
above, gets no contract. Its failing corner $(1, 1)$ was chosen by hand and
checked by Lean; the decider was asked only about the polynomial bounds.

The axiom lists below are the standard three for every checked claim.
`energy_below_three` shows `sorryAx`, as it must: it is the false claim, left
unproved, whose refutation is what Lean checked.
-/

#print axioms energy_formula
#print axioms Decided_energy_in_band.energy_in_band
#print axioms Decided_energy_below_three.energy_below_three
#print axioms original_contract
#print axioms same_function
#print axioms optimised_contract
#print axioms wrong_not_equivalent
#print axioms wrong_breaks_contract
#print axioms four_is_sharp

end Notebook.EnergyOptimization
