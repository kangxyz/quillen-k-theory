/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalMixed
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalMonomorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Closedness of the original projective-line diagonal

The four genuine rectangle maps cover the relative square. On equal-chart rectangles
the diagonal is polynomial evaluation, and on mixed rectangles it is Laurent evaluation.
Thus the original relative diagonal is a closed immersion and the original projection
is separated over every base ring. No sheaf cokernel or projective-bundle formula is asserted.
-/
@[expose] public section
open Quillen

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
/-- Any actual chart-intersection model retains the original diagonal cartesian square. -/
theorem chartIntersection_diagonal_isPullback (R : CommRingCat.{u})
    (j k : Spec (.of (Polynomial R)) ⟶ twoChartLine R)
    (hj : j ≫ projection R = polynomialProjection R)
    (hk : k ≫ projection R = polynomialProjection R)
    {T : Scheme.{u}} (c d : T ⟶ Spec (.of (Polynomial R))) (hc : IsPullback c d j k)
    (m : T ⟶ polynomialSquare R) (hm₁ : m ≫ polynomialFirst R = c)
    (hm₂ : m ≫ polynomialSecond R = d) :
    IsPullback (c ≫ j) m (relativeDiagonal R) (rectangleMap R j k hj hk) := by
  apply (rectangle_diagonal_isPullback R j k hj hk).of_iso
    hc.isoPullback.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.eq_inv_comp]
    simp
  · rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.eq_inv_comp]
    apply pullback.hom_ext
    · simpa only [Category.assoc, polynomialFirst, intersectionToRectangle,
        pullback.lift_fst, IsPullback.isoPullback_hom_fst] using hm₁.symm
    · simpa only [Category.assoc, polynomialSecond, intersectionToRectangle,
        pullback.lift_snd, IsPullback.isoPullback_hom_snd] using hm₂.symm
  · simp
  · simp
/-- The opposite mixed rectangle retains the same original Laurent overlap with swapped legs. -/
theorem oppositeMixedChart_diagonal_isPullback (R : CommRingCat.{u}) :
    IsPullback (laurentMinus R ≫ minusChart R)
      (mixedPolynomialDiagonal R ≫
        (pullbackSymmetry (polynomialProjection R) (polynomialProjection R)).hom)
      (relativeDiagonal R)
      (rectangleMap R (minusChart R) (plusChart R)
        (minusChart_projection R) (plusChart_projection R)) := by
  apply chartIntersection_diagonal_isPullback R _ _ _ _ _ _ (chart_isPullback R).flip
  · simpa only [Category.assoc, polynomialFirst, polynomialSecond,
      pullbackSymmetry_hom_comp_fst] using
      mixedPolynomialDiagonal_second R
  · simpa only [Category.assoc, polynomialSecond, polynomialFirst,
      pullbackSymmetry_hom_comp_snd] using
      mixedPolynomialDiagonal_first R
/-- The original four rectangles as a genuine open cover. -/
def diagonalRectangleCover (R : CommRingCat.{u}) : (relativeSquare R).OpenCover where
  I₀ := Bool × Bool
  X _ := polynomialSquare R
  f := diagonalRectangle R
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨diagonalRectangles_cover R, inferInstance⟩
/-- Closedness of the chosen actual diagonal pullback model transfers to the canonical pullback. -/
theorem closed_diagonal_pullback_of_model {T V : Scheme.{u}} (R : CommRingCat.{u})
    (a : T ⟶ twoChartLine R) (b : T ⟶ V) (j : V ⟶ relativeSquare R)
    (h : IsPullback a b (relativeDiagonal R) j) [IsClosedImmersion b] :
    IsClosedImmersion (pullback.snd (relativeDiagonal R) j) := by
  have : IsClosedImmersion (h.isoPullback.inv ≫ b) := inferInstance
  simpa only [h.isoPullback_inv_snd] using this
/-- The original relative diagonal is a closed immersion over an arbitrary base ring. -/
theorem isClosedImmersion_relativeDiagonal (R : CommRingCat.{u}) :
    IsClosedImmersion (relativeDiagonal R) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (diagonalRectangleCover R)
  intro b
  change IsClosedImmersion (pullback.snd (relativeDiagonal R) (diagonalRectangle R b))
  rcases b with ⟨a,b⟩
  cases a <;> cases b
  · exact closed_diagonal_pullback_of_model R _ _ _
      (sameChart_diagonal_isPullback R (minusChart R) (minusChart_projection R))
  · exact closed_diagonal_pullback_of_model R _ _ _
      (oppositeMixedChart_diagonal_isPullback R)
  · exact closed_diagonal_pullback_of_model R _ _ _ (mixedChart_diagonal_isPullback R)
  · exact closed_diagonal_pullback_of_model R _ _ _
      (sameChart_diagonal_isPullback R (plusChart R) (plusChart_projection R))
/-- The original structural projection of the two-chart line is separated. -/
theorem isSeparated_projection (R : CommRingCat.{u}) : IsSeparated (projection R) := by
  apply (AlgebraicGeometry.isSeparated_iff (projection R)).mpr
  exact isClosedImmersion_relativeDiagonal R
end AlgebraicGeometry.Scheme.ProjectiveLine
