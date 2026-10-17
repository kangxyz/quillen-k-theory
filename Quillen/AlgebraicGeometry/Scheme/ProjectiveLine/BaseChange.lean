/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.CoefficientSquares
public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Charts
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Flat
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

end AlgebraicGeometry.Scheme.ProjectiveLine
