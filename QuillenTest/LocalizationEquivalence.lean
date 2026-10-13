/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.GroupCompletion.LocalizationEquivalence

/-! # Consumers of the equivalence on the original localization -/

@[expose] public section

noncomputable section

universe u v u₁ v₁ u₂ v₂

open CategoryTheory MonoidalCategory Quillen.GroupCompletion
open scoped MonoidalLeftAction
open Functor.LaxLeftLinear

namespace QuillenTest.LocalizationEquivalence

open Quillen

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  (F : D ⥤ E) [F.LaxLeftLinear C]

example [F.EssSurj] : (Localization.actedMapFunctor (C := C) F).EssSurj := inferInstance

variable [∀ (s : C) (X : D), IsIso (μₗ F s X)]

example [F.Full] : (Localization.actedMapFunctor (C := C) F).Full := inferInstance

example [F.Faithful] : (Localization.actedMapFunctor (C := C) F).Faithful := inferInstance

example [F.Full] [F.Faithful] [F.EssSurj] :
    (Localization.actedMapFunctor (C := C) F).IsEquivalence := inferInstance

example [F.Full] [F.Faithful] [F.EssSurj] : Localization C D ≌ Localization C E :=
  Localization.mapEquivalence F

example [F.Full] {X Y : C × D} (s : C) (f : s ⊗ X.1 ⟶ Y.1)
    (g : s ⊙ₗ F.obj X.2 ⟶ F.obj Y.2) :
    (Localization.actedMapFunctor F).map (Localization.mkHom s f
      (F.preimage (inv (μₗ F s X.2) ≫ g))) =
      Localization.mkHom (X := (X.1, F.obj X.2)) (Y := (Y.1, F.obj Y.2)) s f g := by
  rw [Localization.actedMapFunctor_mkHom, F.map_preimage, IsIso.hom_inv_id_assoc]

example [F.Faithful] {X Y : C × D} (s t : C)
    (f : s ⊗ X.1 ⟶ Y.1) (g : s ⊙ₗ X.2 ⟶ Y.2)
    (f' : t ⊗ X.1 ⟶ Y.1) (g' : t ⊙ₗ X.2 ⟶ Y.2)
    (h : Localization.mkHom (X := (X.1, F.obj X.2)) (Y := (Y.1, F.obj Y.2))
      s f (μₗ F s X.2 ≫ F.map g) =
      Localization.mkHom (X := (X.1, F.obj X.2)) (Y := (Y.1, F.obj Y.2))
        t f' (μₗ F t X.2 ≫ F.map g')) :
    Localization.mkHom s f g = Localization.mkHom t f' g' := by
  apply (Localization.actedMapFunctor F).map_injective
  rw [Localization.actedMapFunctor_mkHom, Localization.actedMapFunctor_mkHom]
  change Localization.mkHom (X := (X.1, F.obj X.2)) (Y := (Y.1, F.obj Y.2))
    s f (μₗ F s X.2 ≫ F.map g) =
    Localization.mkHom (X := (X.1, F.obj X.2)) (Y := (Y.1, F.obj Y.2))
      t f' (μₗ F t X.2 ≫ F.map g')
  exact h

end QuillenTest.LocalizationEquivalence
