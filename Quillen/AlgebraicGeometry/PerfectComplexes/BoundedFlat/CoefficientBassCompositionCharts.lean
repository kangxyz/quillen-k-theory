/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientTransformationComposition
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassConditionalLaws

/-!
# Coefficient Bass Composition Charts

Constructed whole chart faces of the ORIGINAL Bass comparison-composition cube.
The inner polynomial cylinder still needs a compatible three-parameter filler.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The exact restriction of the missing whole comparison square to a polynomial chart. -/
abbrev BoundedFlatCoefficientBassCompositionChartSquare
    (i : originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a))) ⟶
      HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))) :=
  (Homotopy.precomp i (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v))).Square
    (Homotopy.precomp i (boundedFlatCoefficientBassCompositeComparison P u v))
    (Homotopy.precomp i
      (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
        (boundedFlatCoefficientLaurentCompositionHomotopy P u v)))
    (Homotopy.precomp i
      ((boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
        (boundedFlatCoefficientBassSquareComparison P c)))

/-- The complete native plus chart is constructed from the original transposed rectangle.
Its span boundary includes exactly the terminal pause present in the fixed span homotopy. -/
def boundedFlatCoefficientBassCompositionPlusChart :
    BoundedFlatCoefficientBassCompositionChartSquare P u v
      (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))) := by
  refine (CoefficientTransformationComposition.movingSquare P (underToLaurent R) u v).pauseRight
    |>.ofBoundaryLevels _ _ _ _ ?_ ?_ ?_ ?_
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n))
      (r, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (boundedFlatCoefficientBassSquareComparison P c).map n
      ((boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).level n
        (r, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) = _
    rw [boundedFlatCoefficientPolynomialSpanCompositionHomotopy_inl]
    change (boundedFlatCoefficientBassSquareComparison P c).map n
      (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl

/-- The separate native minus chart retains the inverse-coordinate transformation verbatim. -/
def boundedFlatCoefficientBassCompositionMinusChart :
    BoundedFlatCoefficientBassCompositionChartSquare P u v
      (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))) := by
  refine (CoefficientTransformationComposition.movingSquare P
    (underToLaurentInvert R) u v).pauseRight |>.ofBoundaryLevels _ _ _ _ ?_ ?_ ?_ ?_
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n))
      (r, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (boundedFlatCoefficientBassSquareComparison P c).map n
      ((boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).level n
        (r, (HomotopyPushout.inr
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) = _
    rw [boundedFlatCoefficientPolynomialSpanCompositionHomotopy_inr]
    change (boundedFlatCoefficientBassSquareComparison P c).map n
      (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)) =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl

end Quillen.PerfectComplexes
