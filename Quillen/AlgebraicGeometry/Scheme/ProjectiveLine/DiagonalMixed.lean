/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Polynomial.LaurentDiagonal
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalEvaluation

/-! # The original Laurent diagonal on a mixed rectangle

The literal mixed evaluation ring map induces the two original Laurent overlap legs.
Its surjectivity proves closedness, and the actual overlap is the base change of the
original relative diagonal along the positive-negative rectangle.
-/
@[expose] public section
open Quillen

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent Quillen.PolynomialBaseChange Quillen.PolynomialDiagonal
/-- The original mixed affine diagonal induced by T and its inverse. -/
def mixedPolynomialDiagonal (R : CommRingCat.{u}) :
    Spec (.of (LaurentPolynomial R)) ⟶ polynomialSquare R :=
  Spec.map (CommRingCat.ofHom (mixedEvaluation R)) ≫ (polynomialSquareIso R).hom
@[reassoc (attr := simp)]
theorem mixedPolynomialDiagonal_first (R : CommRingCat.{u}) :
    mixedPolynomialDiagonal R ≫ polynomialFirst R = laurentPlus R := by
  rw [mixedPolynomialDiagonal, Category.assoc, polynomialSquareIso_hom_first]
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  simp [mixedEvaluation]
@[reassoc (attr := simp)]
theorem mixedPolynomialDiagonal_second (R : CommRingCat.{u}) :
    mixedPolynomialDiagonal R ≫ polynomialSecond R = laurentMinus R := by
  rw [mixedPolynomialDiagonal, Category.assoc, polynomialSquareIso_hom_second]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r <;> simp [mixedEvaluation, polynomialMap]
/-- The mixed diagonal is a closed immersion because its original ring map is surjective. -/
instance (R : CommRingCat.{u}) : IsClosedImmersion (mixedPolynomialDiagonal R) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (mixedEvaluation R))) :=
    IsClosedImmersion.spec_of_surjective _ (mixedEvaluation_surjective R)
  exact inferInstanceAs (IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (mixedEvaluation R)) ≫ (polynomialSquareIso R).hom))
/-- The genuine mixed rectangle pulls the original diagonal back to the original Laurent chart. -/
theorem mixedChart_diagonal_isPullback (R : CommRingCat.{u}) :
    IsPullback (laurentPlus R ≫ plusChart R) (mixedPolynomialDiagonal R)
      (relativeDiagonal R)
      (rectangleMap R (plusChart R) (minusChart R)
        (plusChart_projection R) (minusChart_projection R)) := by
  apply (rectangle_diagonal_isPullback R (plusChart R) (minusChart R)
    (plusChart_projection R) (minusChart_projection R)).of_iso
    (chart_isPullback R).isoPullback.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.eq_inv_comp]
    simp
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.eq_inv_comp]
    apply pullback.hom_ext
    · simpa only [Category.assoc, polynomialFirst, intersectionToRectangle,
        pullback.lift_fst, IsPullback.isoPullback_hom_fst] using
        (mixedPolynomialDiagonal_first R).symm
    · simpa only [Category.assoc, polynomialSecond, intersectionToRectangle,
        pullback.lift_snd, IsPullback.isoPullback_hom_snd] using
        (mixedPolynomialDiagonal_second R).symm
  · simp
  · simp
end AlgebraicGeometry.Scheme.ProjectiveLine
