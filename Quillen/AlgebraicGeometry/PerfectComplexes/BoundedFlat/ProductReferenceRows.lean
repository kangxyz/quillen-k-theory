/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1MiddleJoinFace

/-! Actual full row and column reference nodes of the realized composition product. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes.BassH1Join

section Functors
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ E} (e : F₀ ≅ F₁) (f : G₀ ≅ G₁)

/-- The other actual product-composition order is the naturality square of f. -/
theorem composition_pair_iso_other :
    (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod f) =
      isoWhiskerLeft F₀ f ≪≫ isoWhiskerRight e G₁ := by
  apply Iso.ext
  ext X
  exact f.hom.naturality (e.hom.app X)

variable {H : C ⥤ E} (η : H ≅ F₀ ⋙ G₀)
theorem product_row_reference_iso :
    η ≪≫ (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod f) =
      (η ≪≫ isoWhiskerRight e G₀) ≪≫ isoWhiskerLeft F₁ f := by
  rw [BassReferenceMerge.composition_pair_iso, Iso.trans_assoc]

theorem product_column_reference_iso :
    η ≪≫ (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod f) =
      (η ≪≫ isoWhiskerLeft F₀ f) ≪≫ isoWhiskerRight e G₁ := by
  rw [composition_pair_iso_other, Iso.trans_assoc]
end Functors

variable {V W T : Model.{u}} {p q : ℕ}
  (F : V ⟶ T) (F₀ : V ⟶ W) (Fs : Fin (p + 1) → (V ⟶ W))
  (ρ : ∀ i, F₀.functor ≅ (Fs i).functor)
  (G₀ : W ⟶ T) (Gs : Fin (q + 1) → (W ⟶ T))
  (σ : ∀ j, G₀.functor ≅ (Gs j).functor)
  (η : F.functor ≅ (F₀ ≫ G₀).functor)

/-- The exact old product reference, changed only by its supplied actual total normalization iso. -/
def reanchoredProductNode (i : Fin (Quillen.SimplexGrid.dimension p q + 1)) :
    Σ J : V ⟶ T, F.functor ≅ J.functor :=
  ⟨CommonReferenceProduct.vertices Fs Gs i,
    η ≪≫ CommonReferenceProduct.references F₀ Fs ρ G₀ Gs σ i⟩

/-- Every whole fixed row is the original second family after literal fixed precomposition. -/
theorem product_row_nodes (i : Fin (p + 1)) (j : Fin (q + 1)) :
    reanchoredProductNode F F₀ Fs ρ G₀ Gs σ η (Quillen.SimplexGrid.index p q (i, j)) =
      BassH0Merge.preReferenceNode F (Fs i) (η ≪≫ isoWhiskerRight (ρ i) G₀.functor)
        ⟨Gs j, σ j⟩ := by
  unfold reanchoredProductNode CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  dsimp only
  exact congrArg (fun ν : F.functor ≅ (Fs i ≫ Gs j).functor ↦
    (⟨Fs i ≫ Gs j, ν⟩ : Σ J : V ⟶ T, F.functor ≅ J.functor))
    (product_row_reference_iso (ρ i) (σ j) η)

/-- Every fixed column retains the original first family after its literal fixed postcomposition. -/
theorem product_column_nodes (i : Fin (p + 1)) (j : Fin (q + 1)) :
    reanchoredProductNode F F₀ Fs ρ G₀ Gs σ η (Quillen.SimplexGrid.index p q (i, j)) =
      postReferenceNode F (Gs j) (η ≪≫ isoWhiskerLeft F₀.functor (σ j))
        ⟨Fs i, ρ i⟩ := by
  unfold reanchoredProductNode CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  dsimp only
  exact congrArg (fun ν : F.functor ≅ (Fs i ≫ Gs j).functor ↦
    (⟨Fs i ≫ Gs j, ν⟩ : Σ J : V ⟶ T, F.functor ≅ J.functor))
    (product_column_reference_iso (ρ i) (σ j) η)

end Quillen.PerfectComplexes.BassH1Join
