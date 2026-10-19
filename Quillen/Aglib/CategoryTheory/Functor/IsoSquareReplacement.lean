/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Normalizing a square with two specified input replacements

For four categories with independent object and morphism universes, replacing the first
and last functors of a square and then normalizing all four functors agrees with direct
normalization around the original square. The equality retains every supplied isomorphism
and follows from whisker exchange; it requires no additional compatibility equation.
The current consumer identifies the actual normalized tensor input square with the
original coefficient square after its four genuine target normalizations.
The intended upstream owner is `Aglib.CategoryTheory.Functor.IsoSquareReplacement`.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃
namespace CategoryTheory.Functor

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  {P T NT : C₀ ⥤ C₁} {A NA : C₁ ⥤ C₂}
  {B NB : C₀ ⥤ C₃} {Q U NU : C₃ ⥤ C₂}

/-- Two input replacements and four actual normalizations preserve the same original square. -/
theorem isoSquareReplacement_normalization
    (u : T ≅ P) (v : U ≅ Q) (nT : T ≅ NT) (nA : A ≅ NA)
    (nB : B ≅ NB) (nU : U ≅ NU) (r : P ⋙ A ≅ B ⋙ Q) :
    isoWhiskerRight nT.symm NA ≪≫ isoWhiskerLeft T nA.symm ≪≫
      isoWhiskerRight u A ≪≫ r ≪≫ isoWhiskerLeft B v.symm ≪≫
      isoWhiskerLeft B nU ≪≫ isoWhiskerRight nB NU =
    isoWhiskerLeft NT nA.symm ≪≫ isoWhiskerRight (u.symm ≪≫ nT).symm A ≪≫
      r ≪≫ isoWhiskerRight nB Q ≪≫ isoWhiskerLeft NB (v.symm ≪≫ nU) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerRight_comp, Category.assoc]
  rw [← whiskerLeft_comp_whiskerRight_assoc nT.inv nA.inv,
    ← whiskerLeft_comp_assoc, whiskerLeft_comp_whiskerRight nB.hom (v.inv ≫ nU.hom)]

end CategoryTheory.Functor
