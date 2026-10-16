/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Coproduct injections with a zero complementary object

The original selected coproduct injection is invertible when the complementary object is zero.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiEntries
/-- The literal coproduct inclusion is invertible when its other actual object is zero. -/
lemma coprod_inl_isIso_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasBinaryCoproducts C] (X Y : C) (hY : IsZero Y) :
    IsIso (coprod.inl : X ⟶ X ⨿ Y) := by
  let e : X ≅ X ⨿ Y :=
    { hom := coprod.inl
      inv := coprod.desc (𝟙 X) 0
      hom_inv_id := by simp
      inv_hom_id := by
        apply coprod.hom_ext
        · simp
        · exact hY.eq_of_src _ _ }
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

lemma coprod_inr_isIso_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasBinaryCoproducts C] (X Y : C) (hX : IsZero X) :
    IsIso (coprod.inr : Y ⟶ X ⨿ Y) := by
  let e : Y ≅ X ⨿ Y :=
    { hom := coprod.inr
      inv := coprod.desc 0 (𝟙 Y)
      hom_inv_id := by simp
      inv_hom_id := by
        apply coprod.hom_ext
        · exact hX.eq_of_src _ _
        · simp }
  exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩


end Quillen.PerfectComplexes.ProjectiveLine.FlasquePhiEntries
end
end
