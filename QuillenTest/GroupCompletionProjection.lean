/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.GroupCompletion.Projection

/-! # QuillenTest for the actual projection and its cocartesian lifts -/

@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory Quillen.GroupCompletion
open scoped MonoidalLeftAction
namespace QuillenTest.GroupCompletionProjection
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]
  [∀ A : C, (tensorRight A).Faithful]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

example {A B : C} (s : C) (f : s ⊗ A ⟶ B) (X : D) :
    Localization.projection.map (Localization.lift s f X) =
      ActionLocalization.mkHom ⟨s, f⟩ := by simp

example {X Y : C × D} (s : C) (f : s ⊗ X.1 ⟶ Y.1)
    (g g' : s ⊙ₗ X.2 ⟶ Y.2) :
    Localization.mkHom s f g = Localization.mkHom s f g' ↔ g = g' :=
  Localization.mkHom_eq_iff_same_base s f g g'

example {A B T : C} (s : C) (f : s ⊗ A ⟶ B) (X Y : D)
    (w : (⟨B⟩ : ActionLocalization C C) ⟶ ⟨T⟩)
    (h : (⟨(A, X)⟩ : Localization C D) ⟶ ⟨(T, Y)⟩)
    (hh : Localization.projection.map h = ActionLocalization.mkHom ⟨s, f⟩ ≫ w) :
    ∃! l : (⟨(B, s ⊙ₗ X)⟩ : Localization C D) ⟶ ⟨(T, Y)⟩,
      Localization.projection.map l = w ∧ Localization.lift s f X ≫ l = h :=
  Localization.lift_universal s f X Y w h hh

end QuillenTest.GroupCompletionProjection
