/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.CategoryTheory.GroupCompletion.CommonDenominator
import Quillen.CategoryTheory.Localization.RightRoofs

/-! Actual action-localization zigzags admit roofs without any cancellation assumption. -/
universe u v u' v'
open CategoryTheory CategoryTheory.MonoidalCategory Quillen.GroupCompletion
open scoped MonoidalLeftAction
attribute [local instance] CategoryTheory.Localization.groupoid

example {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalLeftAction C D] [IsGroupoid D]
    {X Y : ActionLocalization C D}
    (a : (⊤ : MorphismProperty (ActionLocalization C D)).Q.obj X ⟶
      (⊤ : MorphismProperty (ActionLocalization C D)).Q.obj Y) :
    ∃ Z, ∃ p : X ⟶ Z, ∃ q : Y ⟶ Z,
      a = (⊤ : MorphismProperty (ActionLocalization C D)).Q.map p ≫
        inv ((⊤ : MorphismProperty (ActionLocalization C D)).Q.map q) :=
  Quillen.GroupoidLocalization.exists_right_roof
    ActionLocalization.exists_common_right_multiple a
