/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductReferenceRows

/-! Exact postcomposition and reference cancellation for original full node families. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes.BassH1Join
variable {V W T U : Model.{u}} {I : Type v}

/-- Actual reference change commutes with fixed postcomposition. -/
theorem anchor_post_node {F K : V ⟶ T} {H : V ⟶ W} (J : W ⟶ T)
    (η : F.functor ≅ K.functor) (ρ : K.functor ≅ (H ≫ J).functor)
    (N : Σ G : V ⟶ W, H.functor ≅ G.functor) :
    BassH0Merge.anchorNode η (postReferenceNode K J ρ N) =
      postReferenceNode F J (η ≪≫ ρ) N := by
  rcases N with ⟨G, σ⟩
  exact congrArg (fun ν : F.functor ≅ (G ≫ J).functor ↦
    (⟨G ≫ J, ν⟩ : Σ G : V ⟶ T, F.functor ≅ G.functor)) (Iso.trans_assoc η ρ _).symm

/-- Two actual fixed postcompositions retain the original family and canonical association. -/
theorem post_post_node (F : V ⟶ U) (J : W ⟶ T) (K : T ⟶ U)
    (H : V ⟶ W) {L : V ⟶ T}
    (ρ : L.functor ≅ (H ≫ J).functor) (η : F.functor ≅ (L ≫ K).functor)
    (N : Σ G : V ⟶ W, H.functor ≅ G.functor) :
    postReferenceNode F K η (postReferenceNode L J ρ N) =
      postReferenceNode F (J ≫ K) (η ≪≫ isoWhiskerRight ρ K.functor) N := by
  rcases N with ⟨G, σ⟩
  have hf : ((G ≫ J) ≫ K).functor = (G ≫ (J ≫ K)).functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change η ≪≫ isoWhiskerRight (ρ ≪≫ isoWhiskerRight σ J.functor) K.functor =
    (η ≪≫ isoWhiskerRight ρ K.functor) ≪≫ isoWhiskerRight σ (J ≫ K).functor
  rw [isoWhiskerRight_trans, Iso.trans_assoc]
  rfl

/-- Reanchoring the input family retains its actual reference before postcomposition. -/
theorem post_anchor_node (F : V ⟶ T) (J : W ⟶ T) {H L : V ⟶ W}
    (ρ : F.functor ≅ (H ≫ J).functor) (η : H.functor ≅ L.functor)
    (N : Σ G : V ⟶ W, L.functor ≅ G.functor) :
    postReferenceNode F J ρ (BassH0Merge.anchorNode η N) =
      postReferenceNode F J (ρ ≪≫ isoWhiskerRight η J.functor) N := by
  rcases N with ⟨G, σ⟩
  apply congrArg (fun ν : F.functor ≅ (G ≫ J).functor ↦
    (⟨G ≫ J, ν⟩ : Σ G : V ⟶ T, F.functor ≅ G.functor))
  exact (isoWhiskerRight_trans η σ J.functor ▸ Iso.trans_assoc ρ
    (isoWhiskerRight η J.functor) (isoWhiskerRight σ J.functor)).symm

variable (F : V ⟶ T) (J : W ⟶ T) (H : V ⟶ W)
  (D : I → Σ G : V ⟶ W, H.functor ≅ G.functor)

/-- One full node cancels the genuine reference iso for every fixed postcomposed node. -/
theorem post_eq_of_node {ρ σ : F.functor ≅ (H ≫ J).functor} (j : I)
    (he : postReferenceNode F J ρ (D j) = postReferenceNode F J σ (D j)) (i : I) :
    postReferenceNode F J ρ (D i) = postReferenceNode F J σ (D i) := by
  have hs : (postReferenceNode F J ρ (D j)).2 = (postReferenceNode F J σ (D j)).2 :=
    eq_of_heq (Sigma.mk.inj he).2
  change ρ ≪≫ isoWhiskerRight (D j).2 J.functor =
    σ ≪≫ isoWhiskerRight (D j).2 J.functor at hs
  have hc := congrArg (fun ν ↦ ν ≪≫ (isoWhiskerRight (D j).2 J.functor).symm) hs
  have hρ : ρ = σ := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hc
  exact congrArg (fun η ↦ postReferenceNode F J η (D i)) hρ

/-- Full native row representations and one full shared node determine the whole row. -/
theorem post_families_match
    {N M : I → Σ G : V ⟶ T, F.functor ≅ G.functor}
    {ρ σ : F.functor ≅ (H ≫ J).functor}
    (hN : ∀ i, N i = postReferenceNode F J ρ (D i))
    (hM : ∀ i, M i = postReferenceNode F J σ (D i))
    (j : I) (he : N j = M j) (i : I) : N i = M i :=
  (hN i).trans ((post_eq_of_node F J H D j
    ((hN j).symm.trans (he.trans (hM j))) i).trans (hM i).symm)

end Quillen.PerfectComplexes.BassH1Join
