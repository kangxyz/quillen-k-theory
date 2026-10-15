/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts
public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialLaurentFlat
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Coefficient change for the original two-chart projective line

The map is glued from the actual polynomial coefficient maps. The original polynomial and Laurent
projection squares are cartesian by the original ring pushouts, over arbitrary commutative rings.
-/
@[expose] public section

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent

open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The coefficient map glued from the original two polynomial chart maps. -/
def coefficientMap : twoChartLine S ⟶ twoChartLine R :=
  pushout.desc (Spec.map (polynomialMap f) ≫ plusChart R)
    (Spec.map (polynomialMap f) ≫ minusChart R) (by
      rw [← Category.assoc, ← laurentMap_plus f, Category.assoc,
        overlap_equation, ← Category.assoc, laurentMap_minus f, Category.assoc])

@[reassoc (attr := simp)] lemma plusChart_coefficientMap :
    plusChart S ≫ coefficientMap f = Spec.map (polynomialMap f) ≫ plusChart R :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)] lemma minusChart_coefficientMap :
    minusChart S ≫ coefficientMap f = Spec.map (polynomialMap f) ≫ minusChart R :=
  pushout.inr_desc _ _ _

/-- The glued coefficient map retains the original structural projections. -/
@[reassoc] lemma coefficientMap_projection :
    coefficientMap f ≫ projection R = projection S ≫ Spec.map f := by
  apply pushout.hom_ext
  · change plusChart S ≫ _ = plusChart S ≫ _
    simp [polynomialMap_projection]
  · change minusChart S ≫ _ = minusChart S ≫ _
    simp [polynomialMap_projection]

/-- The original polynomial coefficient square is cartesian. -/
lemma polynomialProjection_isPullback :
    IsPullback (polynomialProjection S) (Spec.map (polynomialMap f))
      (Spec.map f) (polynomialProjection R) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (polynomial_isPushout f)

/-- The original Laurent coefficient square is cartesian. -/
lemma laurentProjection_isPullback :
    IsPullback (laurentProjection S) (Spec.map (laurentMap f))
      (Spec.map f) (laurentProjection R) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (laurent_isPushout f)

/-- Coefficient change gives the actual cartesian positive-overlap square. -/
lemma laurentPlus_isPullback :
    IsPullback (laurentPlus S) (Spec.map (laurentMap f))
      (Spec.map (polynomialMap f)) (laurentPlus R) := by
  apply IsPullback.of_right (h₁₂ := polynomialProjection S)
    (h₂₂ := polynomialProjection R) _ (laurentMap_plus f).symm
    (polynomialProjection_isPullback f)
  simpa only [laurentPlus_projection] using laurentProjection_isPullback f

/-- Coefficient change gives the actual cartesian inverse-coordinate overlap square. -/
lemma laurentMinus_isPullback :
    IsPullback (laurentMinus S) (Spec.map (laurentMap f))
      (Spec.map (polynomialMap f)) (laurentMinus R) := by
  apply IsPullback.of_right (h₁₂ := polynomialProjection S)
    (h₂₂ := polynomialProjection R) _ (laurentMap_minus f).symm
    (polynomialProjection_isPullback f)
  simpa only [laurentMinus_projection] using laurentProjection_isPullback f

end AlgebraicGeometry.Scheme.ProjectiveLine
