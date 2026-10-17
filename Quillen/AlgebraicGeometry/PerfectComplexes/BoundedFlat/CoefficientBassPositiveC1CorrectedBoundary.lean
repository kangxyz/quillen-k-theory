/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.CarrierSquareDescent
public import Quillen.Topology.Path.NullWordEvaluation
public import Quillen.Topology.Prespectrum.ConeCompositionCorrectionEvaluation
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1ReassociationPieces

/-! The ordinary carrier correction and its exact original boundary word. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1CorrectedBoundary
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveC1ReassociationPieces
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The full lower edge of the supplied initial square. -/
def lowerPath : Path (CoefficientBassPositiveC1InitialMovingNull.first P p q (0, 0))
    (minusTip P p q) where
  toFun s := CoefficientBassPositiveC1InitialMovingNull.parameter P p q (0, s)
  continuous_toFun := by fun_prop
  source' := CoefficientBassPositiveC1InitialMovingNull.parameter_left P p q 0
  target' := CoefficientBassPositiveC1InitialMovingNull.parameter_right P p q 0

/-- The complete initial left edge joins the actual lower and upper source points. -/
def leftPath : Path (CoefficientBassPositiveC1InitialMovingNull.first P p q (0, 0))
    (chartTop P p q 0) where
  toFun r := CoefficientBassPositiveC1InitialMovingNull.first P p q (r, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- All four whole boundaries are proved in the carrier, before any native evaluation. -/
def initialSquare : CarrierPathSquare.Square (lowerPath P p q) (upperWord P p q)
    (leftPath P p q) (Path.refl (minusTip P p q)) where
  parameter := CoefficientBassPositiveC1InitialMovingNull.parameter P p q
  at_zero _ := rfl
  at_one s := (upperWord_apply P p q s).symm
  left r := CoefficientBassPositiveC1InitialMovingNull.parameter_left P p q r
  right r := CoefficientBassPositiveC1InitialMovingNull.parameter_right P p q r

/-- Reassociation retains each original path and its original independent comparison clock. -/
def correction := Path.Homotopy.transAssoc
  (firstPath P p q) (secondPath P p q) (thirdPath P p q)

/-- The corrected upper path has the exact target parentheses of the original correction. -/
def correctedUpper :=
  (firstPath P p q).trans ((secondPath P p q).trans (thirdPath P p q))

/-- The original collapse followed by whiskered R, retaining the constant right edge. -/
def correctedBoundary : (lowerPath P p q).Homotopy
    (((leftPath P p q).trans (correctedUpper P p q)).trans
      (Path.refl (minusTip P p q)).symm) :=
  (initialSquare P p q).toBoundary.trans
    (((Path.Homotopy.refl (leftPath P p q)).hcomp (correction P p q)).hcomp
      ((Path.Homotopy.refl (Path.refl (minusTip P p q))).symm))

/-- The proposed ordinary square is continuous by the proved compact quotient descent. -/
def correctedSquare : CarrierPathSquare.Square (lowerPath P p q) (correctedUpper P p q)
    (leftPath P p q) (Path.refl (minusTip P p q)) :=
  CarrierPathSquare.boundarySquare (correctedBoundary P p q)

/-- Every value of the original corrected boundary word is retained under collapse. -/
theorem correctedSquare_collapse (z : I × I) :
    (correctedSquare P p q).parameter (ThreeSideSquare.collapse z) =
      correctedBoundary P p q z :=
  CarrierPathSquare.boundaryParameter_collapse (correctedBoundary P p q) z

/-- The exact original native R, including its source and target ofLevels identifications. -/
abbrev nativeCorrection := coneSquareCompositionNullComparison
  (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
  (boundedFlatPerfectPrespectrumMap (laurentPlus P b))
  (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map p)))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map p)))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map q)))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
  (boundedFlatCoefficientPlusSquareHomotopy P p)
  (boundedFlatCoefficientPlusSquareHomotopy P q)

/-- All-time ordinary R evaluation follows from the proved three whole path images. -/
theorem correction_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n x (correction P p q (r, s)) =
      (nativeCorrection P p q).level n (r, (s, input P n x)) := by
  have hc := Path.Evaluation.transAssoc (evaluate P p q n x)
    (firstPath P p q) (secondPath P p q) (thirdPath P p q)
    ((nativeFirst P p q).path n (input P n x))
    ((nativeSecond P p q).path n (input P n x))
    ((nativeThird P p q).path n (input P n x))
    (fun t ↦ firstPath_native P p q n t x)
    (fun t ↦ secondPath_native P p q n t x)
    (fun t ↦ thirdPath_native P p q n t x) r s
  exact hc.trans (ConeCompositionPieces.correction_apply
    (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map p)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map q)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
    (boundedFlatCoefficientPlusSquareHomotopy P p)
    (boundedFlatCoefficientPlusSquareHomotopy P q) n r s (input P n x)).symm

end Quillen.PerfectComplexes.CoefficientBassPositiveC1CorrectedBoundary
