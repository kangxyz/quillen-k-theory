/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.CategoryTheory.Triangulated.Basic

/-! # Natural triangle transport through specified endpoint isomorphisms -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pretriangulated
namespace Quillen.TriangleTransport
variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C] [HasShift C ℤ]
  (A : J ⥤ Triangle C) {F₁ F₂ F₃ : J ⥤ C}
  (e₁ : F₁ ≅ A ⋙ Triangle.π₁) (e₂ : F₂ ≅ A ⋙ Triangle.π₂)
  (e₃ : F₃ ≅ A ⋙ Triangle.π₃)

/-- Transport all three actual triangle arrows through the specified endpoint isos. -/
def functor : J ⥤ Triangle C :=
  Triangle.functorMk
    (e₁.hom ≫ whiskerLeft A Triangle.π₁Toπ₂ ≫ e₂.inv)
    (e₂.hom ≫ whiskerLeft A Triangle.π₂Toπ₃ ≫ e₃.inv)
    (e₃.hom ≫ whiskerLeft A Triangle.π₃Toπ₁ ≫
      whiskerRight e₁.inv (shiftFunctor C (1 : ℤ)))

/-- The transport preserves the actual original triangle functor naturally. -/
def iso : functor A e₁ e₂ e₃ ≅ A := by
  refine Triangle.functorIsoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_
  · apply NatTrans.ext
    funext j
    dsimp [functor, Triangle.functorMk]
    simp [Category.assoc]
  · apply NatTrans.ext
    funext j
    dsimp [functor, Triangle.functorMk]
    simp [Category.assoc]
  · apply NatTrans.ext
    funext j
    dsimp [functor, Triangle.functorMk]
    simp [Category.assoc, ← CategoryTheory.Functor.map_comp]
end Quillen.TriangleTransport
