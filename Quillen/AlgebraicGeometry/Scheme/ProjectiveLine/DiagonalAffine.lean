/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.RingTheory.Polynomial.BivariateRegular
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.AffinePlane
public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalCoordinates
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.BaseChange
public import Quillen.Aglib.AlgebraicGeometry.Modules.RankOne.AffineMonomorphisms
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

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent

open Quillen


noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
end AlgebraicGeometry.Scheme.ProjectiveLine

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
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
end AlgebraicGeometry.Scheme.ProjectiveLine

namespace AlgebraicGeometry.Scheme.ProjectiveLine
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
end AlgebraicGeometry.Scheme.ProjectiveLine
