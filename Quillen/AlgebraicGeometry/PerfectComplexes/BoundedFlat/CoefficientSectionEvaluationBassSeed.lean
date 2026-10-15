/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationSourceLeg

/-!
# The original raw native Bass seed and its unit comparison

The raw target retains the original native coefficient projection, forward Laurent unit,
positive-chart source null and parameter-correct loop structure. The complete unit-evaluation
pasting survives its actual cone inclusion. A comparison with the original strict native seed
also requires cone descent and comparison of the original source nulls.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}

/-- The actual forward Laurent unit on the original native coefficient projection. -/
def boundedFlatCoefficientLaurentUnitHomotopy (P : Over (Spec R)) (a : Under R) :=
  boundedFlatPerfectUnitHomotopy (laurentProjection P a)
    (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
      (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right))

/-- Parameter-correct looping of the original raw native two-chart cone. -/
def boundedFlatCoefficientBassStep (P : Over (Spec R)) (a : Under R) : LoopPrespectrum :=
  parameterLooping (mappingCone (boundedFlatCoefficientBassSquareComparison P a))

/-- The original raw seed conjugates the actual forward unit by its positive source null. -/
def boundedFlatCoefficientBassTransition (P : Over (Spec R)) (a : Under R) :
    originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      boundedFlatCoefficientBassStep P a :=
  ((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).nullLoopMap
    (boundedFlatCoefficientBassLaurentNullHomotopy P a)

/-- Every output-loop point keeps the original unit and both original source-null legs. -/
theorem boundedFlatCoefficientBassTransition_apply (P : Over (Spec R)) (a : Under R)
    (n : ℕ) (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (s : unitInterval) :
    Path.toContinuousMap ((boundedFlatCoefficientBassTransition P a).map n x) s =
      (((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).conjugateToZero
          (boundedFlatCoefficientBassLaurentNullHomotopy P a)).level n (s, x) := rfl

variable {P Q : Over (Spec R)} (f : P ⟶ Q)

/-- Original Laurent evaluation followed by the actual raw native cone inclusion. -/
def boundedFlatCoefficientFullOpenBassLaurentMovement (a : Under R) :=
  (boundedFlatCoefficientSectionEvaluationHomotopy
    (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a))
    (𝟙 (op P), (laurentUnderCoefficient R).app a)).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))

/-- The original fine unit evaluated into the original raw Laurent cone corner. -/
def boundedFlatCoefficientFullOpenBassEvaluationOldUnit (a : Under R) :=
  (boundedFlatCoefficientFullOpenLaurentEvaluationOldUnit f a).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))

/-- Actual base evaluation followed by the raw native forward unit and cone inclusion. -/
def boundedFlatCoefficientFullOpenBassEvaluationNewUnit (a : Under R) :=
  (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
    (boundedFlatCoefficientLaurentUnitHomotopy P a)).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))

/-- The actual original unit square keeps its whole pasted boundary inside the raw native cone. -/
def boundedFlatCoefficientFullOpenBassEvaluationUnitPasting (a : Under R) :
    ((boundedFlatCoefficientFullOpenBassEvaluationOldUnit f a).trans
      (boundedFlatCoefficientFullOpenBassLaurentMovement (P := P) a)).RelHomotopy
    ((boundedFlatCoefficientFullOpenBassLaurentMovement (P := P) a).trans
      (boundedFlatCoefficientFullOpenBassEvaluationNewUnit (P := P) a)) := by
  simpa only [Homotopy.postcomp_trans,
    boundedFlatCoefficientFullOpenBassEvaluationOldUnit,
    boundedFlatCoefficientFullOpenBassEvaluationNewUnit,
    boundedFlatCoefficientFullOpenBassLaurentMovement,
    boundedFlatCoefficientFullOpenLaurentEvaluationNewUnit,
    boundedFlatCoefficientLaurentUnitHomotopy, laurentProjection, coefficientMap] using
    (boundedFlatCoefficientFullOpenLaurentEvaluationUnitPasting f a).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))

end Quillen.PerfectComplexes
