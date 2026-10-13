/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.CategoryTheory.GroupCompletion.IteratedFiberEquivalence

/-! # The genuine strict fiber of the iterated projection -/
noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

example (X : D) [(MonoidalLeftAction.actionRight C X).Faithful] :
    Localization C C ≌ Functor.Fiber (iteratedSecondProjection (C := C)) ⟨X⟩ :=
  iteratedSecondFiberEquivalence X

example (X : D) (A : Localization C C) :
    (iteratedFiberEntry X).obj A = ⟨(A.obj.1, ⟨(A.obj.2, X)⟩)⟩ :=
  iteratedFiberEntry_obj X A

example (X : D) {A B : Localization C C} (f : A ⟶ B) :
    iteratedSecondProjection.map ((iteratedFiberEntry X).map f) =
      𝟙 (⟨X⟩ : ActionLocalization C D) :=
  iteratedFiberEntry_projection_map X f
