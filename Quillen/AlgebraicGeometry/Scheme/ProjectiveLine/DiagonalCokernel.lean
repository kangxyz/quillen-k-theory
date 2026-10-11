/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalLocalCokernel
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalSpecModels
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalMonomorphism
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.OpenCoverExactness

/-! # The genuine twisted diagonal short exact sequence

The four original affine rectangles prove that the original incidence and diagonal
quotient maps form a short exact sequence on the genuine relative square. The target is
the actual diagonal pushforward of the original quotient line. The original quotient map
has the cokernel universal property over every base ring, including the zero ring.
No projective-bundle or generation theorem is inferred here.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.Scheme.ProjectiveLine
open PolynomialLaurent Quillen.SchemeSheaf Quillen.PolynomialDiagonal
/-- The original quotient arrow is a cokernel on the actual plus-plus affine rectangle. -/
def diagonalPlusPlusCokernel (R : CommRingCat.{u}) :
    IsColimit (CokernelCofork.ofπ
      ((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
        (specRectangle R (plusChart R) (plusChart R) (plusChart_projection R)
          (plusChart_projection R)))).g
      ((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
        (specRectangle R (plusChart R) (plusChart R) (plusChart_projection R)
          (plusChart_projection R)))).zero) := by
  let s : Γ(polynomialSquare R, ⊤) := rectangleFirstCoordinate R - rectangleSecondCoordinate R
  have hk : RingHom.ker (diagonalEvaluation R).hom =
      Ideal.span {(rectangleSectionsIso R).hom.hom s} := by
    dsimp only [s]
    simp only [map_sub, rectangleSectionsIso_first R, rectangleSectionsIso_second R]
    rw [diagonalEvaluation_ker, ← neg_sub, Ideal.span_singleton_neg]
  have hs : (diagonalEvaluation R).hom ((rectangleSectionsIso R).hom.hom s) = 0 := by
    change (rectangleSectionsIso R).hom.hom s ∈ RingHom.ker (diagonalEvaluation R).hom
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  exact diagonalSpecSequenceCokernel R (plusChart R) (plusChart R) (plusChart_projection R)
    (plusChart_projection R)
    (diagonalEvaluation R) (plusChart R) (equalSpec_diagonal_isPullback R (plusChart R)
      (plusChart_projection R))
    (rectangleLineIso R (plusChart R) (plusChart R) (plusChart_projection R) (plusChart_projection
      R)
      (tautologicalPullbackPlusIso R))
    (rectangleQuotientIso R (plusChart R) (plusChart R) (plusChart_projection R)
      (plusChart_projection R)
      (tautologicalQuotientPullbackPlusIso R))
    s (diagonalIncidence_plus_plus R) hs hk (diagonalEvaluation_surjective R)
/-- The original quotient arrow is a cokernel on the actual plus-minus affine rectangle. -/
def diagonalPlusMinusCokernel (R : CommRingCat.{u}) :
    IsColimit (CokernelCofork.ofπ
      ((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
        (specRectangle R (plusChart R) (minusChart R) (plusChart_projection R)
          (minusChart_projection R)))).g
      ((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
        (specRectangle R (plusChart R) (minusChart R) (plusChart_projection R)
          (minusChart_projection R)))).zero) := by
  let s : Γ(polynomialSquare R, ⊤) := rectangleFirstCoordinate R * rectangleSecondCoordinate R - 1
  have hk : RingHom.ker (CommRingCat.ofHom (mixedEvaluation R)).hom =
      Ideal.span {(rectangleSectionsIso R).hom.hom s} := by
    dsimp only [s]
    simp only [map_sub, map_mul, map_one, rectangleSectionsIso_first R,
      rectangleSectionsIso_second R]
    exact mixedEvaluation_ker R
  have hs : (CommRingCat.ofHom (mixedEvaluation R)).hom ((rectangleSectionsIso R).hom.hom s) = 0
    := by
    change (rectangleSectionsIso R).hom.hom s ∈ RingHom.ker (CommRingCat.ofHom (mixedEvaluation
      R)).hom
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  exact diagonalSpecSequenceCokernel R (plusChart R) (minusChart R) (plusChart_projection R)
    (minusChart_projection R)
    (CommRingCat.ofHom (mixedEvaluation R)) (laurentPlus R ≫ plusChart R)
      (mixedSpec_diagonal_isPullback R)
    (rectangleLineIso R (plusChart R) (minusChart R) (plusChart_projection R)
      (minusChart_projection R)
      (tautologicalPullbackPlusIso R))
    (rectangleQuotientIso R (plusChart R) (minusChart R) (plusChart_projection R)
      (minusChart_projection R)
      (tautologicalQuotientPullbackMinusIso R))
    s (diagonalIncidence_plus_minus R) hs hk (mixedEvaluation_surjective R)
/-- The original quotient arrow is a cokernel on the actual minus-plus affine rectangle. -/
def diagonalMinusPlusCokernel (R : CommRingCat.{u}) :
    IsColimit (CokernelCofork.ofπ
      ((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
        (specRectangle R (minusChart R) (plusChart R) (minusChart_projection R)
          (plusChart_projection R)))).g
      ((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
        (specRectangle R (minusChart R) (plusChart R) (minusChart_projection R)
          (plusChart_projection R)))).zero) := by
  let s : Γ(polynomialSquare R, ⊤) := 1 - rectangleFirstCoordinate R * rectangleSecondCoordinate R
  have hk : RingHom.ker (oppositeMixedEvaluation R).hom =
      Ideal.span {(rectangleSectionsIso R).hom.hom s} := by
    dsimp only [s]
    simp only [map_sub, map_mul, map_one, rectangleSectionsIso_first R,
      rectangleSectionsIso_second R]
    exact oppositeMixedEvaluation_ker R
  have hs : (oppositeMixedEvaluation R).hom ((rectangleSectionsIso R).hom.hom s) = 0 := by
    change (rectangleSectionsIso R).hom.hom s ∈ RingHom.ker (oppositeMixedEvaluation R).hom
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  exact diagonalSpecSequenceCokernel R (minusChart R) (plusChart R) (minusChart_projection R)
    (plusChart_projection R)
    (oppositeMixedEvaluation R) (laurentMinus R ≫ minusChart R)
      (oppositeMixedSpec_diagonal_isPullback R)
    (rectangleLineIso R (minusChart R) (plusChart R) (minusChart_projection R)
      (plusChart_projection R)
      (tautologicalPullbackMinusIso R))
    (rectangleQuotientIso R (minusChart R) (plusChart R) (minusChart_projection R)
      (plusChart_projection R)
      (tautologicalQuotientPullbackPlusIso R))
    s (diagonalIncidence_minus_plus R) hs hk (oppositeMixedEvaluation_surjective R)
/-- The original quotient arrow is a cokernel on the actual minus-minus affine rectangle. -/
def diagonalMinusMinusCokernel (R : CommRingCat.{u}) :
    IsColimit (CokernelCofork.ofπ
      ((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
        (specRectangle R (minusChart R) (minusChart R) (minusChart_projection R)
          (minusChart_projection R)))).g
      ((diagonalIncidenceSequence R).map (Scheme.Modules.restrictFunctor
        (specRectangle R (minusChart R) (minusChart R) (minusChart_projection R)
          (minusChart_projection R)))).zero) := by
  let s : Γ(polynomialSquare R, ⊤) := rectangleSecondCoordinate R - rectangleFirstCoordinate R
  have hk : RingHom.ker (diagonalEvaluation R).hom =
      Ideal.span {(rectangleSectionsIso R).hom.hom s} := by
    dsimp only [s]
    simp only [map_sub, rectangleSectionsIso_first R, rectangleSectionsIso_second R]
    exact diagonalEvaluation_ker R
  have hs : (diagonalEvaluation R).hom ((rectangleSectionsIso R).hom.hom s) = 0 := by
    change (rectangleSectionsIso R).hom.hom s ∈ RingHom.ker (diagonalEvaluation R).hom
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  exact diagonalSpecSequenceCokernel R (minusChart R) (minusChart R) (minusChart_projection R)
    (minusChart_projection R)
    (diagonalEvaluation R) (minusChart R) (equalSpec_diagonal_isPullback R (minusChart R)
      (minusChart_projection R))
    (rectangleLineIso R (minusChart R) (minusChart R) (minusChart_projection R)
      (minusChart_projection R)
      (tautologicalPullbackMinusIso R))
    (rectangleQuotientIso R (minusChart R) (minusChart R) (minusChart_projection R)
      (minusChart_projection R)
      (tautologicalQuotientPullbackMinusIso R))
    s (diagonalIncidence_minus_minus R) hs hk (diagonalEvaluation_surjective R)
end Quillen.Scheme.ProjectiveLine

namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf
/-- The four original affine-spectrum rectangles in the relative square. -/
def diagonalSpecRectangle (R : CommRingCat.{u}) (b : Bool × Bool) :
    Spec (.of (Polynomial (Polynomial R))) ⟶ relativeSquare R :=
  specRectangle R (polynomialChart R b.1) (polynomialChart R b.2)
    (polynomialChart_projection R b.1) (polynomialChart_projection R b.2)
/-- Each original spectrum rectangle is open. -/
instance (R : CommRingCat.{u}) (b : Bool × Bool) :
    IsOpenImmersion (diagonalSpecRectangle R b) :=
  inferInstanceAs (IsOpenImmersion (specRectangle R _ _ _ _))
/-- The original affine-spectrum rectangles jointly cover the actual relative square. -/
theorem diagonalSpecRectangles_cover (R : CommRingCat.{u}) :
    ∀ x : relativeSquare R, ∃ (b : Bool × Bool)
      (y : Spec (.of (Polynomial (Polynomial R)))), diagonalSpecRectangle R b y = x := by
  intro x
  obtain ⟨b, y, hy⟩ := diagonalRectangles_cover R x
  obtain ⟨z, hz⟩ := (polynomialSquareIso R).hom.homeomorph.surjective y
  simp only [Scheme.Hom.homeomorph_apply] at hz
  refine ⟨b, z, ?_⟩
  change diagonalRectangle R b ((polynomialSquareIso R).hom z) = x
  rw [hz, hy]
/-- The literal incidence and quotient maps are short exact on every original rectangle. -/
theorem diagonalIncidenceSequence_restrict_shortExact (R : CommRingCat.{u}) (b : Bool × Bool) :
    ((diagonalIncidenceSequence R).map
      (Scheme.Modules.restrictFunctor (diagonalSpecRectangle R b))).ShortExact := by
  have : Mono (diagonalIncidence R) := mono_diagonalIncidence R
  let T := (diagonalIncidenceSequence R).map
    (Scheme.Modules.restrictFunctor (diagonalSpecRectangle R b))
  have hc : IsColimit (CokernelCofork.ofπ T.g T.zero) := by
    rcases b with ⟨a, b⟩
    cases a <;> cases b
    · exact diagonalMinusMinusCokernel R
    · exact diagonalMinusPlusCokernel R
    · exact diagonalPlusMinusCokernel R
    · exact diagonalPlusPlusCokernel R
  exact { exact := T.exact_of_g_is_cokernel hc
          mono_f := inferInstanceAs (Mono ((Scheme.Modules.restrictFunctor
            (diagonalSpecRectangle R b)).map (diagonalIncidence R)))
          epi_g := epi_of_isColimit_cofork hc }
/-- The genuine diagonal sequence uses the original pulled-back line, quotient, and diagonal map. -/
theorem diagonalIncidenceSequence_shortExact (R : CommRingCat.{u}) :
    (diagonalIncidenceSequence R).ShortExact :=
  shortExact_of_restrict_openCover
    (fun _ : Bool × Bool => Spec (.of (Polynomial (Polynomial R))))
    (diagonalSpecRectangle R) (diagonalSpecRectangles_cover R) (diagonalIncidenceSequence R)
    (diagonalIncidenceSequence_restrict_shortExact R)
/-- The original diagonal quotient map is the actual cokernel of the original incidence map. -/
def diagonalQuotientIsCokernel (R : CommRingCat.{u}) :
    IsColimit (CokernelCofork.ofπ (diagonalQuotientMap R) (diagonalIncidence_quotient R)) := by
  have := (diagonalIncidenceSequence_shortExact R).epi_g
  exact (diagonalIncidenceSequence_shortExact R).exact.gIsCokernel
end Quillen.Scheme.ProjectiveLine
