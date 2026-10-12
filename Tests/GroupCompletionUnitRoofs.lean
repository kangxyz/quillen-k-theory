/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
import Quillen.CategoryTheory.GroupCompletion.UnitRoofs

/-! Actual completed zero loops have single numerators, stable under original translations. -/
universe u v
open CategoryTheory CategoryTheory.MonoidalCategory Quillen.GroupCompletion

example {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]
    {P Q : C} (g : P ⟶ Q) :
    Localization.unitArrow (𝟙 P) ≫ ActionLocalization.ofHom (g, g) =
      Localization.unitArrow (𝟙 Q) := Localization.unitArrow_diagonal g

example {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [IsGroupoid C]
    (a : End ((Localization.completionFunctor (C := C)).obj ⟨𝟙_ C, 𝟙_ C⟩)) :
    ∃ P : C, ∃ g : P ⟶ P, a = Localization.numeratorLoop g :=
  Localization.exists_numeratorLoop a

example {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]
    {P : C} (g : P ⟶ P) (s : C) :
    Localization.numeratorLoop g = Localization.numeratorLoop (s ◁ g) :=
  Localization.numeratorLoop_translation g s
