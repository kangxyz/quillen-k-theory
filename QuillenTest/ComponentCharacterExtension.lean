/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.CategoryTheory.ObjectProperty.ExtensionByConstant
public import Quillen.CategoryTheory.Localization.RightReachable
public import Mathlib.CategoryTheory.Discrete.Basic

/-! Component extension preserves both the selected character and the outside constant. -/
@[expose] public section
noncomputable section
open CategoryTheory
namespace ComponentCharacterExtensionTests

def selected : ObjectProperty (Discrete Bool) := fun X => X.as = true

def branch : selected.FullSubcategory ⥤ Discrete ℕ :=
  (Functor.const _).obj (Discrete.mk 5)

theorem selected_stable {X Y : Discrete Bool} (f : X ⟶ Y) : selected X ↔ selected Y := by
  have h := Discrete.eq_of_hom f
  simp only [selected, h]

example : (Quillen.ObjectProperty.extensionByConstant selected branch (Discrete.mk 7)
    selected_stable).obj (Discrete.mk true) = Discrete.mk 5 := by
  simp [Quillen.ObjectProperty.extensionByConstant, Quillen.ObjectProperty.extensionObject,
    selected, branch]
example : (Quillen.ObjectProperty.extensionByConstant selected branch (Discrete.mk 7)
    selected_stable).obj (Discrete.mk false) = Discrete.mk 7 := by
  simp [Quillen.ObjectProperty.extensionByConstant,
    Quillen.ObjectProperty.extensionObject, selected]
example : selected.ι ⋙ Quillen.ObjectProperty.extensionByConstant selected branch (Discrete.mk 7)
    selected_stable ≅ branch :=
  Quillen.ObjectProperty.extensionByConstantIso _ _ _ _

example (b : Bool) : Quillen.GroupoidLocalization.RightReachable (Discrete.mk b) (Discrete.mk b) :=
  Quillen.GroupoidLocalization.rightReachable_self _
end ComponentCharacterExtensionTests
