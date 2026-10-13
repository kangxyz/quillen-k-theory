/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.GroupCompletion.UnitEntry

/-! # The original acted-on category with a fixed first coordinate -/

@[expose] public section
open CategoryTheory MonoidalCategory
universe u v u' v'
namespace Quillen.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- Include the acted-on category while retaining the specified first coordinate. -/
def fixedFirstEntry (A : C) : D ⥤ Localization C D where
  obj X := ⟨(A, X)⟩
  map f := ActionLocalization.ofHom (𝟙 A, f)
  map_id X := ActionLocalization.ofHom_id (A, X)
  map_comp {X Y Z} f g := by
    simpa using ActionLocalization.ofHom_comp (C := C)
      (X := (A, X)) (Y := (A, Y)) (Z := (A, Z)) (𝟙 A, f) (𝟙 A, g)

/-- At the tensor unit this is precisely the original unit entry. -/
theorem fixedFirstEntry_unit :
    fixedFirstEntry (D := D) (𝟙_ C) = unitEntry := rfl

/-- The actual first-coordinate inclusion respects identity identifications. -/
theorem fixedFirstEntry_map_eqToHom (A : C) {X Y : D} (h : X = Y) :
    (fixedFirstEntry A).map (eqToHom h) = eqToHom (congrArg (fixedFirstEntry A).obj h) :=
  by subst h; simp

end Quillen.GroupCompletion.Localization
