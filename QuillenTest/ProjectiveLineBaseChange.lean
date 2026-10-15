/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.BaseChangeGluing
public import Mathlib.Data.ZMod.Basic

/-! Consumers retain original coefficient maps and their cartesian overlap universal property. -/
@[expose] public section

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.ProjectiveLineBaseChange

open Quillen

/-- Compatible original positive-chart and Laurent maps have a unique actual Laurent lift. -/
theorem original_positive_overlap_lift {R S : CommRingCat.{u}} (f : R ⟶ S)
    {T : Scheme.{u}} (a : T ⟶ Spec (.of (Polynomial S)))
    (b : T ⟶ Spec (.of (LaurentPolynomial R)))
    (h : a ≫ Spec.map (polynomialMap f) = b ≫ laurentPlus R) :
    ∃! l : T ⟶ Spec (.of (LaurentPolynomial S)),
      l ≫ laurentPlus S = a ∧ l ≫ Spec.map (laurentMap f) = b := by
  let P := laurentPlus_isPullback f
  refine ⟨P.lift a b h, ⟨P.lift_fst _ _ _, P.lift_snd _ _ _⟩, ?_⟩
  intro l hl
  exact P.hom_ext (hl.1.trans (P.lift_fst _ _ _).symm)
    (hl.2.trans (P.lift_snd _ _ _).symm)

/-- The inverse-coordinate chart retains the same original gluing map and base projection. -/
theorem original_negative_projection {R S : CommRingCat.{u}} (f : R ⟶ S) :
    minusChart S ≫ coefficientMap f ≫ projection R = polynomialProjection S ≫ Spec.map f := by
  rw [coefficientMap_projection, minusChart_projection_assoc]

/-- Compatible maps to the original projective line and changed base lift uniquely through the
original coefficient-change scheme, including its original structural projection. -/
theorem original_projective_base_change_lift {R S : CommRingCat.{u}} (f : R ⟶ S)
    {T : Scheme.{u}} (a : T ⟶ twoChartLine R) (b : T ⟶ Spec S)
    (h : a ≫ projection R = b ≫ Spec.map f) :
    ∃! l : T ⟶ twoChartLine S, l ≫ coefficientMap f = a ∧ l ≫ projection S = b := by
  let P := coefficientMap_isPullback f
  refine ⟨P.lift a b h, ⟨P.lift_fst _ _ _, P.lift_snd _ _ _⟩, ?_⟩
  intro l hl
  exact P.hom_ext (hl.1.trans (P.lift_fst _ _ _).symm)
    (hl.2.trans (P.lift_snd _ _ _).symm)

/-- The actual pullback identification retains both literal original maps. -/
theorem original_pullback_coordinates {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (coefficientMap_isPullback f).isoPullback.hom ≫ pullback.fst _ _ = coefficientMap f ∧
      (coefficientMap_isPullback f).isoPullback.hom ≫ pullback.snd _ _ = projection S :=
  ⟨(coefficientMap_isPullback f).isoPullback_hom_fst,
    (coefficientMap_isPullback f).isoPullback_hom_snd⟩

/-- Empty geometry over the zero ring remains included in actual cartesian base change. -/
theorem original_zero_base :
    IsPullback (coefficientMap (𝟙 (CommRingCat.of (ZMod 1))))
      (projection (.of (ZMod 1))) (projection (.of (ZMod 1)))
      (Spec.map (𝟙 (CommRingCat.of (ZMod 1)))) :=
  coefficientMap_isPullback _

end QuillenTest.ProjectiveLineBaseChange
