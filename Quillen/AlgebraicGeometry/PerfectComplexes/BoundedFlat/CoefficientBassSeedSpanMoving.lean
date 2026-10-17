/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedSpanNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedSpanBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedSpanSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedSpanCast

/-! Whole span naturality, with the actual polynomial cylinder and chosen composition tracks. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedSpanMoving
open CoefficientBassSeedSpanNaturality
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The center vertices move by the original whole seed coefficient homotopy. -/
abbrev center := (boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).symm
/-- Both polynomial vertices move by the original whole seed coefficient homotopy. -/
abbrev chart := (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
  ((polynomialUnderFunctor R).map u)).symm

/-- The equal-composite filler yields the actual moving polynomial leg square. -/
def legSquare : (leftTrack P u).Square (rightTrack P u)
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) (chart P u))
    ((center P u).postcomp
      (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app b))) := by
  let p := (polynomialUnderCoefficient R).app a
  let q := (polynomialUnderFunctor R).map u
  let p' := u
  let q' := (polynomialUnderCoefficient R).app b
  let h : p ≫ q = p' ≫ q' := ((polynomialUnderCoefficient R).naturality u).symm
  let S := CoefficientBassSeedSpanSquare.square
    (CoefficientBassSeedSpanBoundary.boundary P p q p' q' h)
  apply S.ofBoundaryLevels
  · intro n
    apply Homotopy.trans_level_congr
    · let C := (boundedFlatCoefficientCompositionHomotopy P p q).symm.trans
        ((boundedFlatCoefficientCompositionHomotopy P p' q').cast
          (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap (coefficientMap P k)) h.symm) rfl)
      have hs : (boundedFlatCoefficientPolynomialSquareHomotopy P u).level n = C.level n :=
        (boundedFlatPerfectPrespectrumSquareHomotopy_level _ _ _ _ _ n).trans (by
          apply Homotopy.trans_level_congr
          · apply Homotopy.symm_level_congr
            dsimp only [boundedFlatCoefficientCompositionHomotopy]
            exact (Homotopy.cast_level _ _ _ n).symm
          · dsimp only [boundedFlatCoefficientCompositionHomotopy]
            exact (Homotopy.cast_level _ _ _ n).trans
              ((Homotopy.cast_level _ _ _ n).trans
                (Homotopy.cast_level _ _ _ n)).symm)
      have he := Homotopy.postcomp_level_congr _ _
        (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj b)) n hs
      exact he.trans (by
        dsimp only [C]
        rw [Homotopy.postcomp_trans]
        apply Homotopy.trans_level_congr <;> rfl)
    · rfl
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · have he := CoefficientBassSeedSpanCast.precomp_cast_pasting_level
        (BassMWhole.stepComposition P p q) (BassMWhole.stepComposition P p' q')
        (congrArg (boundedFlatCoefficientBassStepMap P) h.symm)
        (boundedFlatCoefficientBassTransition P a)
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm rfl n
      apply ContinuousMap.ext
      intro z
      dsimp only [CoefficientBassSecondCoefficientProjection.polynomialSquare,
        CoefficientBassSecondCoefficientProjection.naturalitySquare,
        CoefficientBassSeedSpanBoundary.Kp, CoefficientBassSeedSpanBoundary.Km,
        p, q, p', q', h, Functor.id_obj, Functor.id_map] at he ⊢
      exact DFunLike.congr_fun he z
  · intro n
    rfl
  · intro n
    rfl

/-- Quotient descent retains both moving charts and the complete original middle cylinder. -/
def movingSpan : Homotopy (leftSpan P u) (rightSpan P u) :=
  HomotopyPushout.descSquareHomotopy _ _
    ((chart P u).postcomp (HomotopyPushout.inl _ _))
    ((chart P u).postcomp (HomotopyPushout.inr _ _))
    (HomotopyPushout.identicalLegMovingSquare _ _
      (leftTrack P u) (rightTrack P u) (center P u) (chart P u) (legSquare P u))

/-- The actual first seed span map is natural up to the constructed whole homotopy. -/
def spanNaturality : Homotopy
    (boundedFlatCoefficientPolynomialSpanMap P u ≫ CoefficientBassSeedPushoutComparison.spanMap P b)
    (CoefficientBassSeedPushoutComparison.spanMap P a ≫
      CoefficientBassSecondCoefficientProjection.spanMap P u) :=
  (leftReduction P u).trans ((movingSpan P u).trans (rightReduction P u).symm)

end Quillen.PerfectComplexes.CoefficientBassSeedSpanMoving
