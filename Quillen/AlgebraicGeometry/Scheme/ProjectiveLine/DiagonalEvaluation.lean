/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalAffine
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Original equal-coordinate affine diagonal

Polynomial evaluation has its literal principal kernel and induces the original
diagonal in the affine rectangle. Both same-chart base-change diagrams retain
the actual relative diagonal and original rectangle maps over an arbitrary base ring.
-/
@[expose] public section
open Quillen

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent Quillen.PolynomialBaseChange
/-- Evaluation on the actual equal-coordinate affine diagonal. -/
def diagonalEvaluation (R : CommRingCat.{u}) :
    CommRingCat.of (Polynomial (Polynomial R)) ⟶ CommRingCat.of (Polynomial R) :=
  CommRingCat.ofHom (Polynomial.evalRingHom Polynomial.X)
/-- The original diagonal in the affine polynomial rectangle. -/
def polynomialDiagonal (R : CommRingCat.{u}) :
    Spec (.of (Polynomial R)) ⟶ polynomialSquare R :=
  pullback.lift (𝟙 _) (𝟙 _) (by simp)
/-- The evaluation map retains the first original projection. -/
theorem diagonalEvaluation_first (R : CommRingCat.{u}) :
    Spec.map (diagonalEvaluation R) ≫ (polynomialSquareIso R).hom ≫ polynomialFirst R = 𝟙 _ := by
  rw [polynomialSquareIso_hom_first]
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact Polynomial.eval_C
/-- The evaluation map retains the second original projection. -/
theorem diagonalEvaluation_second (R : CommRingCat.{u}) :
    Spec.map (diagonalEvaluation R) ≫ (polynomialSquareIso R).hom ≫ polynomialSecond R = 𝟙 _ := by
  rw [polynomialSquareIso_hom_second, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x <;> simp [diagonalEvaluation, polynomialMap]
/-- The original affine diagonal is literally induced by polynomial evaluation. -/
theorem diagonalEvaluation_eq_diagonal (R : CommRingCat.{u}) :
    Spec.map (diagonalEvaluation R) ≫ (polynomialSquareIso R).hom = polynomialDiagonal R := by
  apply pullback.hom_ext
  · simpa only [polynomialDiagonal, pullback.lift_fst, Category.assoc, polynomialFirst] using
      diagonalEvaluation_first R
  · simpa only [polynomialDiagonal, pullback.lift_snd, Category.assoc, polynomialSecond] using
      diagonalEvaluation_second R
/-- The original evaluation ring map is surjective over every base ring. -/
theorem diagonalEvaluation_surjective (R : CommRingCat.{u}) :
    Function.Surjective (diagonalEvaluation R).hom := Polynomial.eval_surjective _
/-- Its kernel is the actual equal-coordinate equation. -/
theorem diagonalEvaluation_ker (R : CommRingCat.{u}) :
    RingHom.ker (diagonalEvaluation R).hom =
      Ideal.span {Polynomial.X - Polynomial.C Polynomial.X} := Polynomial.ker_evalRingHom _
/-- The actual affine diagonal is a closed immersion over every base ring. -/
instance (R : CommRingCat.{u}) : IsClosedImmersion (polynomialDiagonal R) := by
  have : IsClosedImmersion (Spec.map (diagonalEvaluation R)) :=
    IsClosedImmersion.spec_of_surjective _ (diagonalEvaluation_surjective R)
  rw [← diagonalEvaluation_eq_diagonal]
  infer_instance
/-- Same-chart base change retains the actual polynomial diagonal. -/
theorem sameChart_diagonal_isPullback (R : CommRingCat.{u})
    (j : Spec (.of (Polynomial R)) ⟶ twoChartLine R) [IsOpenImmersion j]
    (hj : j ≫ projection R = polynomialProjection R) :
    IsPullback j (polynomialDiagonal R) (relativeDiagonal R) (rectangleMap R j j hj hj) := by
  apply (rectangle_diagonal_isPullback R j j hj hj).of_iso
    (asIso (pullback.fst j j)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · apply pullback.hom_ext <;>
      simp [intersectionToRectangle, polynomialDiagonal, fst_eq_snd_of_mono_eq]
  · simp
  · simp
end AlgebraicGeometry.Scheme.ProjectiveLine
