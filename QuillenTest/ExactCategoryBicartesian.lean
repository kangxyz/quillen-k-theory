/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Aglib.CategoryTheory.ExactCategory.Basic
import Quillen.Aglib.CategoryTheory.ExactCategory.Bicartesian

open CategoryTheory.ExactCategory


/-!
# Consumers of bicartesian admissible pushouts

These examples recover a base-change isomorphism and solve a simultaneous
lifting problem using an arbitrary original pushout square.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C) {A B A' B' : C}
variable {i : A ⟶ B} {f : A ⟶ A'} {g : B ⟶ B'} {j : A' ⟶ B'}

example (hi : E.inflation i) (sq : IsPushout i f g j) [IsIso g] : IsIso f :=
  (E.isPullback_of_inflation_isPushout hi sq).isIso_snd_of_isIso

example (hi : E.inflation i) (sq : IsPushout i f g j)
    {T : C} (a : T ⟶ B) (b : T ⟶ A') (h : a ≫ g = b ≫ j) :
    ∃! l : T ⟶ A, l ≫ i = a ∧ l ≫ f = b := by
  let pb := E.isPullback_of_inflation_isPushout hi sq
  refine ⟨pb.lift a b h, ⟨pb.lift_fst a b h, pb.lift_snd a b h⟩, ?_⟩
  intro l hl
  apply pb.hom_ext
  · simpa only [IsPullback.lift_fst] using hl.1
  · simpa only [IsPullback.lift_snd] using hl.2
