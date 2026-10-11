/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalMonomorphism
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of actual diagonal monicity and cartesian chart intersections -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Tests.ProjectiveLineDiagonalMonomorphism
/-- Cancellation uses the literal original incidence morphism on arbitrary sheaf arrows. -/
theorem original_incidence_cancel (R : CommRingCat.{u})
    {M : (relativeSquare R).Modules}
    (f g : M ⟶ (Scheme.Modules.pullback (relativeFirst R)).obj (tautologicalLine R))
    (h : f ≫ diagonalIncidence R = g ≫ diagonalIncidence R) : f = g := by
  have := mono_diagonalIncidence R
  exact (cancel_mono (diagonalIncidence R)).mp h
/-- Every point of the actual relative square has an original rectangle preimage. -/
theorem original_rectangle_preimage (R : CommRingCat.{u}) (x : relativeSquare R) :
    ∃ (b : Bool × Bool) (y : polynomialSquare R), diagonalRectangle R b y = x :=
  diagonalRectangles_cover R x
/-- The affine isomorphism retains both original polynomial projection coordinates. -/
theorem original_affine_coordinates (R : CommRingCat.{u}) :
    (rectangleSectionsIso R).hom.hom (rectangleFirstCoordinate R) =
        Polynomial.C Polynomial.X ∧
      (rectangleSectionsIso R).hom.hom (rectangleSecondCoordinate R) = Polynomial.X :=
  ⟨rectangleSectionsIso_first R, rectangleSectionsIso_second R⟩
/-- A genuine commuting mixed-chart square lifts uniquely to the actual chart intersection. -/
theorem mixed_intersection_lift (R : CommRingCat.{u}) {Z : Scheme.{u}}
    (a : Z ⟶ twoChartLine R) (b : Z ⟶ polynomialSquare R)
    (hab : a ≫ relativeDiagonal R = b ≫
      rectangleMap R (plusChart R) (minusChart R)
        (plusChart_projection R) (minusChart_projection R)) :
    ∃! l : Z ⟶ pullback (plusChart R) (minusChart R),
      l ≫ pullback.fst _ _ ≫ plusChart R = a ∧
        l ≫ intersectionToRectangle R (plusChart R) (minusChart R)
          (plusChart_projection R) (minusChart_projection R) = b := by
  let h := rectangle_diagonal_isPullback R (plusChart R) (minusChart R)
    (plusChart_projection R) (minusChart_projection R)
  refine ⟨h.lift a b hab, ⟨h.lift_fst a b hab, h.lift_snd a b hab⟩, ?_⟩
  intro l hl
  exact h.hom_ext (hl.1.trans (h.lift_fst a b hab).symm)
    (hl.2.trans (h.lift_snd a b hab).symm)
/-- The actual global kernel is zero, rather than only its polynomial model. -/
theorem original_kernel_zero (R : CommRingCat.{u}) : IsZero (kernel (diagonalIncidence R)) := by
  have := mono_diagonalIncidence R
  exact isZero_kernel_of_mono _
/-- Monicity survives the nonreduced base without a domain assumption. -/
theorem nonreduced_incidence_mono : Mono (diagonalIncidence (.of (ZMod 4))) :=
  mono_diagonalIncidence _
/-- The original kernel vanishes over the zero ring as well. -/
theorem zero_ring_kernel_zero : IsZero (kernel (diagonalIncidence (.of (ZMod 1)))) :=
  original_kernel_zero _
end Quillen.Tests.ProjectiveLineDiagonalMonomorphism
