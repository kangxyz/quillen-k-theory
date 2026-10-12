/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.CategoryTheory.GroupCompletion.SwitchRight

/-! # The coherent middle functor and its proved right natural arrow -/
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [IsGroupoid C] {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction
example (X : D) : switch ⋙ iteratedFiberEntry (C := C) X ⟶ switchMiddle X :=
  switchedFiberToMiddle X
example (X : D) (A : Localization C C) :
    (switchMiddle X).obj A = ⟨(A.obj.2, ⟨(A.obj.2 ⊗ A.obj.1, A.obj.2 ⊙ₗ X)⟩)⟩ := rfl
