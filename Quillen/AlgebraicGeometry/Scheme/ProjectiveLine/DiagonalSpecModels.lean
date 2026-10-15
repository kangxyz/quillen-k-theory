/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalClosedImmersion

/-! # Original spectrum models of the four diagonal rectangles

The actual affine rectangle isomorphism identifies the original diagonal base-change
squares with the literal equal-coordinate and mixed evaluation spectrum maps. The opposite
mixed evaluation retains both original Laurent legs and its signed principal kernel.
-/
@[expose] public section
open Quillen


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.PolynomialDiagonal PolynomialLaurent
/-- The actual equal-coordinate spectrum square retains the original diagonal and chart map. -/
theorem equalSpec_diagonal_isPullback (R : CommRingCat.{u})
    (j : Spec (.of (Polynomial R)) ⟶ twoChartLine R) [IsOpenImmersion j]
    (hj : j ≫ projection R = polynomialProjection R) :
    IsPullback j (Spec.map (diagonalEvaluation R)) (relativeDiagonal R)
      ((polynomialSquareIso R).hom ≫ rectangleMap R j j hj hj) := by
  apply (sameChart_diagonal_isPullback R j hj).of_iso
    (Iso.refl _) (Iso.refl _) (polynomialSquareIso R).symm (Iso.refl _)
  · simp
  · simp [← diagonalEvaluation_eq_diagonal]
  · simp
  · simp
/-- The mixed spectrum square uses the original evaluation map and original Laurent chart. -/
theorem mixedSpec_diagonal_isPullback (R : CommRingCat.{u}) :
    IsPullback (laurentPlus R ≫ plusChart R)
      (Spec.map (CommRingCat.ofHom (mixedEvaluation R))) (relativeDiagonal R)
      ((polynomialSquareIso R).hom ≫ rectangleMap R (plusChart R) (minusChart R)
        (plusChart_projection R) (minusChart_projection R)) := by
  apply (mixedChart_diagonal_isPullback R).of_iso
    (Iso.refl _) (Iso.refl _) (polynomialSquareIso R).symm (Iso.refl _)
  · simp
  · simp [mixedPolynomialDiagonal]
  · simp
  · simp
end AlgebraicGeometry.Scheme.ProjectiveLine

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent Quillen.PolynomialBaseChange Quillen.PolynomialDiagonal
/-- The original opposite mixed evaluation sends the first variable to T^-1 and the second to T. -/
def oppositeMixedEvaluation (R : CommRingCat.{u}) :
    CommRingCat.of (Polynomial (Polynomial R)) ⟶ CommRingCat.of (LaurentPolynomial R) :=
  CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp (mixedEvaluation R))
/-- Inversion of the actual Laurent ring preserves surjectivity of its original evaluation. -/
theorem oppositeMixedEvaluation_surjective (R : CommRingCat.{u}) :
    Function.Surjective (oppositeMixedEvaluation R).hom :=
  LaurentPolynomial.invert.surjective.comp (mixedEvaluation_surjective R)
/-- The opposite mixed kernel retains the signed incidence equation 1 - t*u. -/
theorem oppositeMixedEvaluation_ker (R : CommRingCat.{u}) :
    RingHom.ker (oppositeMixedEvaluation R).hom =
      Ideal.span {1 - C (X : Polynomial R) * X} := by
  change RingHom.ker (LaurentPolynomial.invert.toRingHom.comp (mixedEvaluation R)) = _
  rw [RingHom.ker_comp_of_injective _ LaurentPolynomial.invert.injective,
    mixedEvaluation_ker]
  rw [← neg_sub, Ideal.span_singleton_neg]
/-- The first opposite coordinate is the original negative overlap leg. -/
theorem oppositeMixedEvaluation_first (R : CommRingCat.{u}) :
    Spec.map (oppositeMixedEvaluation R) ≫ (polynomialSquareIso R).hom ≫
      polynomialFirst R = laurentMinus R := by
  rw [polynomialSquareIso_hom_first]
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  simp [oppositeMixedEvaluation, mixedEvaluation]
/-- The second coordinate is the original positive Laurent overlap leg. -/
theorem oppositeMixedEvaluation_second (R : CommRingCat.{u}) :
    Spec.map (oppositeMixedEvaluation R) ≫ (polynomialSquareIso R).hom ≫
      polynomialSecond R = laurentPlus R := by
  rw [polynomialSquareIso_hom_second]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r <;> simp [oppositeMixedEvaluation, mixedEvaluation, polynomialMap]
/-- The original negative-positive affine rectangle has its actual opposite-evaluation square. -/
theorem oppositeMixedSpec_diagonal_isPullback (R : CommRingCat.{u}) :
    IsPullback (laurentMinus R ≫ minusChart R) (Spec.map (oppositeMixedEvaluation R))
      (relativeDiagonal R)
      ((polynomialSquareIso R).hom ≫ rectangleMap R (minusChart R) (plusChart R)
        (minusChart_projection R) (plusChart_projection R)) := by
  have h := chartIntersection_diagonal_isPullback R (minusChart R) (plusChart R)
    (minusChart_projection R) (plusChart_projection R)
    (laurentMinus R) (laurentPlus R) (chart_isPullback R).flip
    (Spec.map (oppositeMixedEvaluation R) ≫ (polynomialSquareIso R).hom)
    (oppositeMixedEvaluation_first R) (oppositeMixedEvaluation_second R)
  apply h.of_iso (Iso.refl _) (Iso.refl _) (polynomialSquareIso R).symm (Iso.refl _) <;> simp
end AlgebraicGeometry.Scheme.ProjectiveLine
