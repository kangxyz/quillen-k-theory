/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalClosedImmersion
public import Mathlib.Data.ZMod.Basic

/-! # Original diagonal ring-map and closed-immersion consumers -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Quillen.PolynomialDiagonal Quillen.Scheme.ProjectiveLine
open Quillen.Scheme.PolynomialLaurent
namespace QuillenTest.ProjectiveLineDiagonalClosedImmersion

open Quillen
/-- Every polynomial is the image of the literal equal-coordinate evaluation. -/
theorem equal_coordinate_lift (R : CommRingCat.{u}) (p : Polynomial R) :
    ∃ q, (diagonalEvaluation R).hom q = p := diagonalEvaluation_surjective R p
/-- Vanishing under the original evaluation is precisely divisibility by its signed equation. -/
theorem equal_coordinate_kernel (R : CommRingCat.{u}) (p : Polynomial (Polynomial R)) :
    (diagonalEvaluation R).hom p = 0 ↔ ∃ q, q * (X - C X) = p := by
  change p ∈ RingHom.ker (diagonalEvaluation R).hom ↔ _
  rw [diagonalEvaluation_ker, Ideal.mem_span_singleton']
/-- Every Laurent section has a lift through the original mixed evaluation. -/
theorem mixed_coordinate_lift (R : CommRingCat.{u}) (p : LaurentPolynomial R) :
    ∃ q, mixedEvaluation R q = p := mixedEvaluation_surjective R p
/-- The mixed kernel retains the literal positive-negative incidence equation. -/
theorem mixed_coordinate_kernel (R : CommRingCat.{u}) (p : Polynomial (Polynomial R)) :
    mixedEvaluation R p = 0 ↔ ∃ q, q * (C (X : Polynomial R) * X - 1) = p := by
  change p ∈ RingHom.ker (mixedEvaluation R) ↔ _
  rw [mixedEvaluation_ker, Ideal.mem_span_singleton']
/-- Both coordinates of the original mixed diagonal are the actual Laurent overlap legs. -/
theorem original_mixed_coordinates (R : CommRingCat.{u}) :
    mixedPolynomialDiagonal R ≫ polynomialFirst R = laurentPlus R ∧
      mixedPolynomialDiagonal R ≫ polynomialSecond R = laurentMinus R :=
  ⟨mixedPolynomialDiagonal_first R, mixedPolynomialDiagonal_second R⟩
/-- A commuting mixed-rectangle square has a unique lift to the original Laurent chart. -/
theorem original_laurent_lift (R : CommRingCat.{u}) {Z : Scheme.{u}}
    (a : Z ⟶ twoChartLine R) (b : Z ⟶ polynomialSquare R)
    (hab : a ≫ relativeDiagonal R = b ≫ rectangleMap R (plusChart R) (minusChart R)
      (plusChart_projection R) (minusChart_projection R)) :
    ∃! l : Z ⟶ Spec (.of (LaurentPolynomial R)),
      l ≫ (laurentPlus R ≫ plusChart R) = a ∧ l ≫ mixedPolynomialDiagonal R = b := by
  let h := mixedChart_diagonal_isPullback R
  refine ⟨h.lift a b hab, ⟨h.lift_fst a b hab, h.lift_snd a b hab⟩, ?_⟩
  intro l hl
  exact h.hom_ext (hl.1.trans (h.lift_fst a b hab).symm)
    (hl.2.trans (h.lift_snd a b hab).symm)
/-- The genuine diagonal is closed even over a nonreduced ring. -/
theorem nonreduced_diagonal_closed :
    IsClosedImmersion (relativeDiagonal (.of (ZMod 4))) := isClosedImmersion_relativeDiagonal _
/-- Separatedness includes the zero-ring base. -/
theorem zero_ring_projection_separated :
    IsSeparated (projection (.of (ZMod 1))) := isSeparated_projection _
end QuillenTest.ProjectiveLineDiagonalClosedImmersion
