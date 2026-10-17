/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.OppositeMixedEvaluation
public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalClosedImmersion

/-! # Original spectrum models of the four diagonal rectangles

The actual affine rectangle isomorphism identifies the original diagonal base-change
squares with the literal equal-coordinate and mixed evaluation spectrum maps. The opposite
mixed evaluation retains both original Laurent legs and its signed principal kernel.
-/
@[expose] public section

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent

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
open PolynomialLaurent Quillen.PolynomialDiagonal
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
