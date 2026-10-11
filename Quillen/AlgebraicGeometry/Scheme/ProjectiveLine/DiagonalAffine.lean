/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalCoordinates
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.BaseChange
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineMonomorphisms
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-! # Affine models of the original relative diagonal

The genuine polynomial rectangle is identified with the spectrum of the iterated polynomial
ring, retaining both original coordinates. The four incidence scalars are regular over
every base ring, so each original rectangle pullback of incidence is monic. The pullback
of the original diagonal along a rectangle is the actual intersection of its two charts.
Local cokernel identifications and global short exactness are not asserted here.
-/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.Scheme.ProjectiveLine
open PolynomialLaurent Quillen.PolynomialBaseChange
/-- The actual rectangle is the spectrum of the iterated polynomial ring. -/
def polynomialSquareIso (R : CommRingCat.{u}) :
    Spec (.of (Polynomial (Polynomial R))) ≅ polynomialSquare R :=
  (polynomialProjection_isPullback (CommRingCat.ofHom (Polynomial.C (R := R)))).isoPullback
@[reassoc (attr := simp)]
theorem polynomialSquareIso_hom_first (R : CommRingCat.{u}) :
    (polynomialSquareIso R).hom ≫ polynomialFirst R =
      polynomialProjection (.of (Polynomial R)) :=
  (polynomialProjection_isPullback (CommRingCat.ofHom (Polynomial.C (R := R)))).isoPullback_hom_fst
@[reassoc (attr := simp)]
theorem polynomialSquareIso_hom_second (R : CommRingCat.{u}) :
    (polynomialSquareIso R).hom ≫ polynomialSecond R =
      Spec.map (polynomialMap (CommRingCat.ofHom (Polynomial.C (R := R)))) :=
  (polynomialProjection_isPullback (CommRingCat.ofHom (Polynomial.C (R := R)))).isoPullback_hom_snd
/-- The affine section identification induced by the actual rectangle isomorphism. -/
def rectangleSectionsIso (R : CommRingCat.{u}) :
    Γ(polynomialSquare R, ⊤) ≅ CommRingCat.of (Polynomial (Polynomial R)) :=
  Scheme.Γ.mapIso (polynomialSquareIso R).op ≪≫
    Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))
/-- The first original coordinate is the inner polynomial variable. -/
theorem rectangleSectionsIso_first (R : CommRingCat.{u}) :
    (rectangleSectionsIso R).hom.hom (rectangleFirstCoordinate R) =
      Polynomial.C Polynomial.X := by
  change (((polynomialFirst R).appTop ≫ (polynomialSquareIso R).hom.appTop ≫
    (Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))).hom).hom
      (polynomialCoordinate R)) = _
  rw [← Scheme.Hom.comp_appTop_assoc, polynomialSquareIso_hom_first]
  change (((Spec.map (CommRingCat.ofHom Polynomial.C)).appTop ≫
    (Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))).hom).hom
      (polynomialCoordinate R)) = _
  rw [Scheme.ΓSpecIso_naturality]
  simp [polynomialCoordinate]
/-- The second original coordinate is the outer polynomial variable. -/
theorem rectangleSectionsIso_second (R : CommRingCat.{u}) :
    (rectangleSectionsIso R).hom.hom (rectangleSecondCoordinate R) = Polynomial.X := by
  change (((polynomialSecond R).appTop ≫ (polynomialSquareIso R).hom.appTop ≫
    (Scheme.ΓSpecIso (.of (Polynomial (Polynomial R)))).hom).hom
      (polynomialCoordinate R)) = _
  rw [← Scheme.Hom.comp_appTop_assoc, polynomialSquareIso_hom_second]
  rw [Scheme.ΓSpecIso_naturality]
  simp [polynomialCoordinate, polynomialMap]
open scoped nonZeroDivisors
/-- The first diagonal equation is regular over every base ring. -/
theorem diagonalPolynomial_plus_plus_regular (R : CommRingCat.{u}) :
    (Polynomial.C Polynomial.X - Polynomial.X : Polynomial (Polynomial R)) ∈
      (Polynomial (Polynomial R))⁰ := by
  apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
  simp [mem_nonZeroDivisors_iff]
/-- The first mixed diagonal equation has a unit constant coefficient. -/
theorem diagonalPolynomial_plus_minus_regular (R : CommRingCat.{u}) :
    (Polynomial.C Polynomial.X * Polynomial.X - 1 : Polynomial (Polynomial R)) ∈
      (Polynomial (Polynomial R))⁰ := by
  apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
  simp [mem_nonZeroDivisors_iff]
/-- The second mixed diagonal equation has a unit constant coefficient. -/
theorem diagonalPolynomial_minus_plus_regular (R : CommRingCat.{u}) :
    (1 - Polynomial.C Polynomial.X * Polynomial.X : Polynomial (Polynomial R)) ∈
      (Polynomial (Polynomial R))⁰ := by
  apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
  simp
/-- The second diagonal equation is monic in the second variable. -/
theorem diagonalPolynomial_minus_minus_regular (R : CommRingCat.{u}) :
    (Polynomial.X - Polynomial.C Polynomial.X : Polynomial (Polynomial R)) ∈
      (Polynomial (Polynomial R))⁰ := by
  apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
  simp
end Quillen.Scheme.ProjectiveLine

namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf
/-- The original plus-plus incidence scalar is monic on its genuine rectangle. -/
theorem mono_incidenceScalar_plus_plus (R : CommRingCat.{u}) :
    Mono (unitMul (polynomialSquare R)
      (rectangleFirstCoordinate R - rectangleSecondCoordinate R)) := by
  apply mono_unitMul_of_affineModel (.of (Polynomial (Polynomial R))) (polynomialSquareIso R)
  apply mem_nonZeroDivisors_of_injective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
      (.of (Polynomial (Polynomial R)))).hom).1
  change (rectangleSectionsIso R).hom.hom
    (rectangleFirstCoordinate R - rectangleSecondCoordinate R) ∈ _
  rw [map_sub, rectangleSectionsIso_first, rectangleSectionsIso_second]
  exact diagonalPolynomial_plus_plus_regular R
/-- The actual incidence map is monic after the plus-plus rectangle pullback. -/
theorem mono_diagonalIncidence_plus_plus (R : CommRingCat.{u}) :
    Mono ((Scheme.Modules.pullback (rectangleMap R (plusChart R) (plusChart R)
      (plusChart_projection R) (plusChart_projection R))).map
      (diagonalIncidence R)) := by
  have := mono_incidenceScalar_plus_plus R
  have : Mono ((Scheme.Modules.pullback (rectangleMap R (plusChart R) (plusChart R)
      (plusChart_projection R) (plusChart_projection R))).map
      (diagonalIncidence R) ≫
      (rectangleQuotientIso R (plusChart R) (plusChart R)
      (plusChart_projection R) (plusChart_projection R)
        (tautologicalQuotientPullbackPlusIso R)).hom) := by
    rw [diagonalIncidence_plus_plus]
    infer_instance
  exact mono_of_mono _ (rectangleQuotientIso R (plusChart R) (plusChart R)
      (plusChart_projection R) (plusChart_projection R)
    (tautologicalQuotientPullbackPlusIso R)).hom
/-- The original plus-minus incidence scalar is monic on its genuine rectangle. -/
theorem mono_incidenceScalar_plus_minus (R : CommRingCat.{u}) :
    Mono (unitMul (polynomialSquare R)
      (rectangleFirstCoordinate R * rectangleSecondCoordinate R - 1)) := by
  apply mono_unitMul_of_affineModel (.of (Polynomial (Polynomial R))) (polynomialSquareIso R)
  apply mem_nonZeroDivisors_of_injective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
      (.of (Polynomial (Polynomial R)))).hom).1
  change (rectangleSectionsIso R).hom.hom
    (rectangleFirstCoordinate R * rectangleSecondCoordinate R - 1) ∈ _
  rw [map_sub, map_mul, map_one, rectangleSectionsIso_first, rectangleSectionsIso_second]
  exact diagonalPolynomial_plus_minus_regular R
/-- The actual incidence map is monic after the plus-minus rectangle pullback. -/
theorem mono_diagonalIncidence_plus_minus (R : CommRingCat.{u}) :
    Mono ((Scheme.Modules.pullback (rectangleMap R (plusChart R) (minusChart R)
      (plusChart_projection R) (minusChart_projection R))).map
      (diagonalIncidence R)) := by
  have := mono_incidenceScalar_plus_minus R
  have : Mono ((Scheme.Modules.pullback (rectangleMap R (plusChart R) (minusChart R)
      (plusChart_projection R) (minusChart_projection R))).map
      (diagonalIncidence R) ≫
      (rectangleQuotientIso R (plusChart R) (minusChart R)
      (plusChart_projection R) (minusChart_projection R)
        (tautologicalQuotientPullbackMinusIso R)).hom) := by
    rw [diagonalIncidence_plus_minus]
    infer_instance
  exact mono_of_mono _ (rectangleQuotientIso R (plusChart R) (minusChart R)
      (plusChart_projection R) (minusChart_projection R)
    (tautologicalQuotientPullbackMinusIso R)).hom
/-- The original minus-plus incidence scalar is monic on its genuine rectangle. -/
theorem mono_incidenceScalar_minus_plus (R : CommRingCat.{u}) :
    Mono (unitMul (polynomialSquare R)
      (1 - rectangleFirstCoordinate R * rectangleSecondCoordinate R)) := by
  apply mono_unitMul_of_affineModel (.of (Polynomial (Polynomial R))) (polynomialSquareIso R)
  apply mem_nonZeroDivisors_of_injective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
      (.of (Polynomial (Polynomial R)))).hom).1
  change (rectangleSectionsIso R).hom.hom
    (1 - rectangleFirstCoordinate R * rectangleSecondCoordinate R) ∈ _
  rw [map_sub, map_mul, map_one, rectangleSectionsIso_first, rectangleSectionsIso_second]
  exact diagonalPolynomial_minus_plus_regular R
/-- The actual incidence map is monic after the minus-plus rectangle pullback. -/
theorem mono_diagonalIncidence_minus_plus (R : CommRingCat.{u}) :
    Mono ((Scheme.Modules.pullback (rectangleMap R (minusChart R) (plusChart R)
      (minusChart_projection R) (plusChart_projection R))).map
      (diagonalIncidence R)) := by
  have := mono_incidenceScalar_minus_plus R
  have : Mono ((Scheme.Modules.pullback (rectangleMap R (minusChart R) (plusChart R)
      (minusChart_projection R) (plusChart_projection R))).map
      (diagonalIncidence R) ≫
      (rectangleQuotientIso R (minusChart R) (plusChart R)
      (minusChart_projection R) (plusChart_projection R)
        (tautologicalQuotientPullbackPlusIso R)).hom) := by
    rw [diagonalIncidence_minus_plus]
    infer_instance
  exact mono_of_mono _ (rectangleQuotientIso R (minusChart R) (plusChart R)
      (minusChart_projection R) (plusChart_projection R)
    (tautologicalQuotientPullbackPlusIso R)).hom
/-- The original minus-minus incidence scalar is monic on its genuine rectangle. -/
theorem mono_incidenceScalar_minus_minus (R : CommRingCat.{u}) :
    Mono (unitMul (polynomialSquare R)
      (rectangleSecondCoordinate R - rectangleFirstCoordinate R)) := by
  apply mono_unitMul_of_affineModel (.of (Polynomial (Polynomial R))) (polynomialSquareIso R)
  apply mem_nonZeroDivisors_of_injective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
      (.of (Polynomial (Polynomial R)))).hom).1
  change (rectangleSectionsIso R).hom.hom
    (rectangleSecondCoordinate R - rectangleFirstCoordinate R) ∈ _
  rw [map_sub, rectangleSectionsIso_first, rectangleSectionsIso_second]
  exact diagonalPolynomial_minus_minus_regular R
/-- The actual incidence map is monic after the minus-minus rectangle pullback. -/
theorem mono_diagonalIncidence_minus_minus (R : CommRingCat.{u}) :
    Mono ((Scheme.Modules.pullback (rectangleMap R (minusChart R) (minusChart R)
      (minusChart_projection R) (minusChart_projection R))).map
      (diagonalIncidence R)) := by
  have := mono_incidenceScalar_minus_minus R
  have : Mono ((Scheme.Modules.pullback (rectangleMap R (minusChart R) (minusChart R)
      (minusChart_projection R) (minusChart_projection R))).map
      (diagonalIncidence R) ≫
      (rectangleQuotientIso R (minusChart R) (minusChart R)
      (minusChart_projection R) (minusChart_projection R)
        (tautologicalQuotientPullbackMinusIso R)).hom) := by
    rw [diagonalIncidence_minus_minus]
    infer_instance
  exact mono_of_mono _ (rectangleQuotientIso R (minusChart R) (minusChart R)
      (minusChart_projection R) (minusChart_projection R)
    (tautologicalQuotientPullbackMinusIso R)).hom
end Quillen.Scheme.ProjectiveLine

namespace Quillen.Scheme.ProjectiveLine
open PolynomialLaurent
variable (R : CommRingCat.{u})
    (j k : Spec (.of (Polynomial R)) ⟶ twoChartLine R)
    (hj : j ≫ projection R = polynomialProjection R)
    (hk : k ≫ projection R = polynomialProjection R)
/-- The original chart intersection maps to the original polynomial rectangle. -/
def intersectionToRectangle : pullback j k ⟶ polynomialSquare R :=
  pullback.lift (pullback.fst j k) (pullback.snd j k) (by
    calc
      _ = pullback.fst j k ≫ j ≫ projection R := by rw [hj]
      _ = pullback.snd j k ≫ k ≫ projection R := by
        rw [← Category.assoc, ← Category.assoc, pullback.condition]
      _ = _ := by rw [hk])
/-- The actual diagonal base change along an original rectangle is the chart intersection. -/
theorem rectangle_diagonal_isPullback :
    IsPullback (pullback.fst j k ≫ j) (intersectionToRectangle R j k hj hk)
      (relativeDiagonal R) (rectangleMap R j k hj hk) := by
  apply (pullback_map_diagonal_isPullback j k (projection R)).of_iso
    (Iso.refl _) (Iso.refl _) (pullback.congrHom hj hk) (Iso.refl _)
  · simp
  · apply pullback.hom_ext <;> simp [intersectionToRectangle]
  · rfl
  · apply pullback.hom_ext <;> simp [rectangleMap]
end Quillen.Scheme.ProjectiveLine
