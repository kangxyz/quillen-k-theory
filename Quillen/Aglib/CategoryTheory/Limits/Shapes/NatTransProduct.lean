/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Invertibility of original natural-transformation components on binary products

The proof retains the two original product comparisons and naturality squares.
-/

@[expose] public section
noncomputable section

section
universe v u v' u'
open CategoryTheory.Limits
namespace CategoryTheory.NatTrans
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
/-- A natural transformation between product-preserving functors is invertible on a product
when its actual components on the two factors are invertible. -/
theorem isIso_app_prod (F G : C ⥤ D) (α : F ⟶ G) (X Y : C)
    [HasBinaryProduct X Y] [HasBinaryProduct (F.obj X) (F.obj Y)]
    [HasBinaryProduct (G.obj X) (G.obj Y)]
    [PreservesLimit (pair X Y) F] [PreservesLimit (pair X Y) G]
    [IsIso (α.app X)] [IsIso (α.app Y)] : IsIso (α.app (X ⨯ Y)) := by
  have h : α.app (X ⨯ Y) = prodComparison F X Y ≫
      prod.map (α.app X) (α.app Y) ≫ inv (prodComparison G X Y) := by
    apply (cancel_mono (prodComparison G X Y)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    apply prod.hom_ext
    · simpa only [Category.assoc, prodComparison_fst, prodComparison_fst_assoc, prod.map_fst] using
        (α.naturality (prod.fst : X ⨯ Y ⟶ X)).symm
    · simpa only [Category.assoc, prodComparison_snd, prodComparison_snd_assoc, prod.map_snd] using
        (α.naturality (prod.snd : X ⨯ Y ⟶ Y)).symm
  rw [h]
  infer_instance
end CategoryTheory.NatTrans
end
