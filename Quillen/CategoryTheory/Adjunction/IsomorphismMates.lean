/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Invertibility of the original mates along equivalences -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
  {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
/-- Taking mates along equivalence adjunctions preserves the original invertible square. -/
theorem isIso_mateEquiv_of_equivalence_adjunctions
    [L₁.IsEquivalence] [L₂.IsEquivalence] (α : TwoSquare G L₁ L₂ H)
    [IsIso α.natTrans] : IsIso (mateEquiv adj₁ adj₂ α).natTrans := by
  dsimp [mateEquiv]
  infer_instance
/-- Invertible vertical functors make the inverse mate of an invertible square invertible. -/
theorem isIso_mateEquiv_symm_of_equivalences
    [G.IsEquivalence] [H.IsEquivalence] (β : TwoSquare R₁ H G R₂)
    [IsIso β.natTrans] : IsIso ((mateEquiv adj₁ adj₂).symm β).natTrans := by
  let adj₃ := G.asEquivalence.toAdjunction
  let adj₄ := H.asEquivalence.toAdjunction
  let α := (mateEquiv adj₁ adj₂).symm β
  have hβ : IsIso (mateEquiv adj₄ adj₃ β).natTrans :=
    isIso_mateEquiv_of_equivalence_adjunctions adj₄ adj₃ β
  have hc : IsIso (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α.natTrans) := by
    rw [← iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄ α]
    have hx : mateEquiv adj₁ adj₂ α = β := (mateEquiv adj₁ adj₂).apply_symm_apply β
    erw [hx]
    exact hβ
  exact conjugateEquiv_of_iso (adj₁.comp adj₄) (adj₃.comp adj₂) α.natTrans
end CategoryTheory
