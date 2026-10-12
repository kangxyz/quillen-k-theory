/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.CategoryTheory.GroupCompletion.OrbitEntry
import Quillen.CategoryTheory.GroupCompletion.Switch

/-! # The original orbit entry and coordinate switch -/
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open Quillen.GroupCompletion Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
example (X : D) (A : Localization C C) :
    (orbitEntry X).obj A = ⟨(A.obj.1, A.obj.2 ⊙ₗ X)⟩ := rfl
example : Localization C C ≌ Localization C C := switchEquivalence
example : switch (C := C) ⋙ switch = 𝟭 _ := switch_comp_switch
