import Gimle.Forseti.Examples.AIFOutputEnclosure
import Gimle.Forseti.Examples.AIFSlabDrift

/-! What one cell of the AIF moving tube must check, and what the checks give.

A cell module names its slab in the candidate mesh and decides each check below
by kernel evaluation. `drift` and `output` turn passing checks into the cell's
two obligations: the in-tube drift inequality and the output enclosure: the
shifted output `y 1 = x₂ - 2` is at most `6/5` inside the tube. Nothing here is
assumed about a particular slab. -/
namespace AIFSafety.Cell
open Gimle.Forseti Gimle.Forseti.Examples
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix AIFSlabModel

deriving instance DecidableEq for Slab

/-- The drift-block table at error value `ec` is within degree `(9, 3)`, and every
one of its 40 Bernstein matrices has a checked square certificate. -/
def BlockCheck (d : Slab) (ec : ℚ) : Prop :=
  (∀ i j, BernsteinConversion.withinDegree 9 3
      (AIFPolynomialBinding.block d ec i j) = true) ∧
    ∀ a b, (RationalLDL.propose (BernsteinConversion.table 9 3
      (AIFPolynomialBinding.block d ec) a b)).Represents
        (BernsteinConversion.table 9 3 (AIFPolynomialBinding.block d ec) a b)

/-- The four containment-margin matrices have checked square certificates. -/
def ContainmentCheck (d : Slab) : Prop :=
  ∀ i j, (RationalLDL.propose (AIFSlabContainment.errorCoefficients d i j)).Represents
    (AIFSlabContainment.errorCoefficients d i j)

/-- Bézier controls of the output species' center on the slab's two eta edges. -/
def loControls (d : Slab) : Fin 4 → ℚ :=
  AIFOutputEnclosure.hermiteControls d.step (d.loStart 1) (d.loEnd 1)
    (d.loStartSlope 1) (d.loEndSlope 1)

def hiControls (d : Slab) : Fin 4 → ℚ :=
  AIFOutputEnclosure.hermiteControls d.step (d.hiStart 1) (d.hiEnd 1)
    (d.hiStartSlope 1) (d.hiEndSlope 1)

/-- The largest center control, which bounds the output species' center. -/
def centerBound (d : Slab) : ℚ := max
  (max (max (loControls d 0) (loControls d 1)) (max (loControls d 2) (loControls d 3)))
  (max (max (hiControls d 0) (hiControls d 1)) (max (hiControls d 2) (hiControls d 3)))

/-- The center stays below `6/5` with a margin the tube cannot cross: the controls
are below the bound, the gap is positive, and the four output-margin matrices for
that gap have checked square certificates. -/
def OutputCheck (d : Slab) : Prop :=
  (∀ i, loControls d i ≤ centerBound d) ∧ (∀ i, hiControls d i ≤ centerBound d) ∧
    0 < 6/5 - centerBound d ∧
    ∀ i j, (RationalLDL.propose
      (AIFOutputEnclosure.outputCoefficients d (6/5 - centerBound d) i j)).Represents
        (AIFOutputEnclosure.outputCoefficients d (6/5 - centerBound d) i j)

/-- The in-tube drift inequality on one slab. -/
def Drift (d : Slab) : Prop :=
  ∀ t p (e : Fin 4 → ℝ),
    t ∈ Set.Icc (d.tStart : ℝ) ((d.tStart : ℝ) + d.step) →
    p ∈ Set.Icc (d.etaLo : ℝ) (d.etaHi : ℝ) →
    matrixForm (metric d (timeCoordinate d t)) e ≤ 1/40000 →
    energyRate d (timeCoordinate d t) (etaCoordinate d p) e ≤
      (1/100) * (1/40000 - matrixForm (metric d (timeCoordinate d t)) e) - 1/16000000

/-- Tube membership on one slab bounds the shifted output species. -/
def Output (d : Slab) : Prop :=
  ∀ t p (x : Fin 4 → ℝ),
    t ∈ Set.Icc (d.tStart : ℝ) ((d.tStart : ℝ) + d.step) →
    p ∈ Set.Icc (d.etaLo : ℝ) (d.etaHi : ℝ) →
    AIFMesh.tubeEnergy d t p x ≤ 1/40000 → x 1 ≤ 6/5

theorem drift (d : Slab) (negative : BlockCheck d (-3/200))
    (positive : BlockCheck d (3/200)) (containment : ContainmentCheck d)
    (symmetric : AIFSlabData.SymmetricData d)
    (width : 0 < d.step) (ordered : d.etaLo < d.etaHi) : Drift d :=
  AIFSlabDrift.drift_in_tube d
    { symmetric := symmetric
      error := fun i j => RationalLDL.propose (AIFSlabContainment.errorCoefficients d i j)
      errorValid := containment
      negative := .ofComputed d (-3/200) negative.1 negative.2
      positive := .ofComputed d (3/200) positive.1 positive.2 }
    width ordered

theorem output (d : Slab) (check : OutputCheck d)
    (width : 0 < d.step) (ordered : d.etaLo < d.etaHi) : Output d :=
  fun t p x ht hp he =>
    AIFOutputEnclosure.shifted_output_bound d (centerBound d) (le_of_lt check.2.2.1)
      (fun i j => RationalLDL.propose
        (AIFOutputEnclosure.outputCoefficients d (6/5 - centerBound d) i j))
      check.2.2.2 check.1 check.2.1 _ _ (timeCoordinate_mem d width t ht)
      (etaCoordinate_mem d ordered p hp) x he

#print axioms drift
#print axioms output
end AIFSafety.Cell
