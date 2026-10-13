/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalCoordinates
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of the original relative diagonal and four incidence coordinates -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace QuillenTest.ProjectiveLineDiagonalIncidence

open Quillen
/-- The original diagonal is determined by its two original projections. -/
theorem diagonal_unique (R : CommRingCat.{u}) (f : twoChartLine R ⟶ relativeSquare R)
    (h₁ : f ≫ relativeFirst R = 𝟙 _) (h₂ : f ≫ relativeSecond R = 𝟙 _) :
    f = relativeDiagonal R := by
  apply pullback.hom_ext
  · exact h₁.trans (relativeDiagonal_first R).symm
  · exact h₂.trans (relativeDiagonal_second R).symm
/-- Transposing the original diagonal quotient returns the original section comparison. -/
theorem quotient_adjoint (R : CommRingCat.{u}) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (relativeDiagonal R)).homEquiv _ _).symm
      (diagonalQuotientMap R) =
      (sectionPullbackIso (relativeDiagonal R) (relativeSecond R)
        (relativeDiagonal_second R)).hom.app (tautologicalQuotientLine R) := by
  exact Equiv.symm_apply_apply _ _
/-- The short complex retains the original inclusion and original adjoint quotient. -/
theorem original_sequence_maps (R : CommRingCat.{u}) :
    (diagonalIncidenceSequence R).f = diagonalIncidence R ∧
      (diagonalIncidenceSequence R).g = diagonalQuotientMap R := ⟨rfl, rfl⟩
/-- Restricting the actual short complex's first map along the diagonal gives zero. -/
theorem diagonal_restriction_zero (R : CommRingCat.{u}) :
    (Scheme.Modules.pullback (relativeDiagonal R)).map (diagonalIncidenceSequence R).f = 0 :=
  diagonalIncidence_pullback_diagonal R
/-- Original chart conjugation recovers the literal plus-plus scalar. -/
theorem scalar_plus_plus (R : CommRingCat.{u}) :
    (rectangleLineIso R (plusChart R) (plusChart R)
      (plusChart_projection R) (plusChart_projection R)
      (tautologicalPullbackPlusIso R)).inv ≫
    (Scheme.Modules.pullback (rectangleMap R (plusChart R) (plusChart R)
      (plusChart_projection R) (plusChart_projection R))).map
      (diagonalIncidenceSequence R).f ≫
    (rectangleQuotientIso R (plusChart R) (plusChart R)
      (plusChart_projection R) (plusChart_projection R)
      (tautologicalQuotientPullbackPlusIso R)).hom =
      unitMul (polynomialSquare R)
        (rectangleFirstCoordinate R - rectangleSecondCoordinate R) := by
  rw [show (diagonalIncidenceSequence R).f = diagonalIncidence R from rfl,
    diagonalIncidence_plus_plus, Iso.inv_hom_id_assoc]
/-- Original chart conjugation recovers the literal plus-minus scalar. -/
theorem scalar_plus_minus (R : CommRingCat.{u}) :
    (rectangleLineIso R (plusChart R) (minusChart R)
      (plusChart_projection R) (minusChart_projection R)
      (tautologicalPullbackPlusIso R)).inv ≫
    (Scheme.Modules.pullback (rectangleMap R (plusChart R) (minusChart R)
      (plusChart_projection R) (minusChart_projection R))).map
      (diagonalIncidenceSequence R).f ≫
    (rectangleQuotientIso R (plusChart R) (minusChart R)
      (plusChart_projection R) (minusChart_projection R)
      (tautologicalQuotientPullbackMinusIso R)).hom =
      unitMul (polynomialSquare R)
        (rectangleFirstCoordinate R * rectangleSecondCoordinate R - 1) := by
  rw [show (diagonalIncidenceSequence R).f = diagonalIncidence R from rfl,
    diagonalIncidence_plus_minus, Iso.inv_hom_id_assoc]
/-- Original chart conjugation recovers the literal minus-plus scalar. -/
theorem scalar_minus_plus (R : CommRingCat.{u}) :
    (rectangleLineIso R (minusChart R) (plusChart R)
      (minusChart_projection R) (plusChart_projection R)
      (tautologicalPullbackMinusIso R)).inv ≫
    (Scheme.Modules.pullback (rectangleMap R (minusChart R) (plusChart R)
      (minusChart_projection R) (plusChart_projection R))).map
      (diagonalIncidenceSequence R).f ≫
    (rectangleQuotientIso R (minusChart R) (plusChart R)
      (minusChart_projection R) (plusChart_projection R)
      (tautologicalQuotientPullbackPlusIso R)).hom =
      unitMul (polynomialSquare R)
        (1 - rectangleFirstCoordinate R * rectangleSecondCoordinate R) := by
  rw [show (diagonalIncidenceSequence R).f = diagonalIncidence R from rfl,
    diagonalIncidence_minus_plus, Iso.inv_hom_id_assoc]
/-- Original chart conjugation recovers the literal minus-minus scalar. -/
theorem scalar_minus_minus (R : CommRingCat.{u}) :
    (rectangleLineIso R (minusChart R) (minusChart R)
      (minusChart_projection R) (minusChart_projection R)
      (tautologicalPullbackMinusIso R)).inv ≫
    (Scheme.Modules.pullback (rectangleMap R (minusChart R) (minusChart R)
      (minusChart_projection R) (minusChart_projection R))).map
      (diagonalIncidenceSequence R).f ≫
    (rectangleQuotientIso R (minusChart R) (minusChart R)
      (minusChart_projection R) (minusChart_projection R)
      (tautologicalQuotientPullbackMinusIso R)).hom =
      unitMul (polynomialSquare R)
        (rectangleSecondCoordinate R - rectangleFirstCoordinate R) := by
  rw [show (diagonalIncidenceSequence R).f = diagonalIncidence R from rfl,
    diagonalIncidence_minus_minus, Iso.inv_hom_id_assoc]
/-- The nonreduced base retains the actual diagonal annihilation equation. -/
theorem nonreduced_diagonal :
    (Scheme.Modules.pullback (relativeDiagonal (.of (ZMod 4)))).map
      (diagonalIncidence (.of (ZMod 4))) = 0 :=
  diagonalIncidence_pullback_diagonal _
/-- The zero-ring base retains the actual adjoint quotient and incidence composition. -/
theorem zero_ring_sequence :
    diagonalIncidence (.of (ZMod 1)) ≫ diagonalQuotientMap (.of (ZMod 1)) = 0 :=
  diagonalIncidence_quotient _
end QuillenTest.ProjectiveLineDiagonalIncidence
