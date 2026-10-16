/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.AffinePlane
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual diagonal geometry of the polynomial affine plane

The original polynomial evaluation map retains both projections, its actual
kernel equation and surjectivity. Its spectrum is the literal affine diagonal
and a closed immersion over every commutative base ring.
-/
@[expose] public section

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent

open Quillen

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
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
end AlgebraicGeometry.Scheme.ProjectiveLine
