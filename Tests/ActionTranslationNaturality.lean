/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
import Quillen.CategoryTheory.GroupCompletion.ActionTranslationNaturality

/-! Tests for the original translation naturality square. -/
universe u v u' v'
open CategoryTheory MonoidalCategory Quillen.GroupCompletion
open scoped MonoidalLeftAction

example {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [MonoidalCategory C] [MonoidalLeftAction C D]
    (s : C) {X Y : D} (f : X ⟶ Y) :
    ActionLocalization.ofHom (C := C) f ≫ ActionLocalization.translation s Y =
      ActionLocalization.translation s X ≫ ActionLocalization.ofHom (s ⊴ₗ f) :=
  ActionLocalization.ofHom_translation s f
