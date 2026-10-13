/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Rows.NerveBridge

/-! # Original nerve reindexing of the weak-row grid -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Simplicial
universe u v
namespace Quillen.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Restricting the original nerve coordinate restricts the actual chain of weak rows. -/
theorem weakChainToGrid_precomp_nerve {n k l : SimplexCategory}
    (F : ComposableArrows (WeakRows W n) k.len) (α : l ⟶ k) :
    gridMap₂ (𝟙 n) α ⋙ weakChainToGrid W F =
      weakChainToGrid W (α.toOrderHom.monotone.functor ⋙ F) := by
  refine CategoryTheory.Functor.ext
    (F := gridMap₂ (𝟙 n) α ⋙ weakChainToGrid W F)
    (G := weakChainToGrid W (α.toOrderHom.monotone.functor ⋙ F)) (fun _ ↦ rfl) ?_
  intro p q f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end Quillen.Waldhausen.QuotientRows
