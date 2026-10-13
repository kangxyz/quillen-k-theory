/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.CategoryTheory.Localization.CharacterExtension

/-! Nontrivial groupoid consumers of the character extension and its comparison. -/
@[expose] public section
universe u v w w'
noncomputable section
open CategoryTheory Quillen.CharacterExtension
namespace CharacterExtensionTests
variable {C : Type u} {D : Type w} [Groupoid.{v} C] [Groupoid.{w'} D]

theorem groupoidSquares {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    Nonempty (Square (𝟭 C) f g) :=
  ⟨⟨Z, inv f ≫ g, 𝟙 Z, by simp⟩⟩

theorem groupoidCancellation (F : C ⥤ D) {X Y Z : C} (r : X ⟶ Y) (f g : Y ⟶ Z)
    (h : r ≫ (𝟭 C).map f = r ≫ (𝟭 C).map g) : F.map f = F.map g :=
  congrArg F.map ((cancel_epi r).1 h)

example (F : C ⥤ D) :
    𝟭 C ⋙ extension (𝟭 C) F groupoidSquares (groupoidCancellation F)
      (fun X => X) (fun X => 𝟙 X) ≅ F :=
  extensionIso (𝟭 C) F groupoidSquares (groupoidCancellation F) _ _

example (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    fraction (𝟭 C) F groupoidSquares (𝟙 X) f = F.map f :=
  fraction_map (𝟭 C) F groupoidSquares (groupoidCancellation F) f
end CharacterExtensionTests
