/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareBinaryNodes

/-! Full original node families under repeated fixed precomposition and reference cancellation. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH0Merge

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes.BassH1Join
open BassH0Merge
variable {U V W T : Model.{u}} {I : Type v}

/-- Two original fixed precompositions retain their actual full reference association. -/
theorem pre_pre_node (F : U ⟶ T) (P : U ⟶ V) (Q : V ⟶ W) (H : W ⟶ T) {L : V ⟶ T}
    (ρ : L.functor ≅ (Q ≫ H).functor) (η : F.functor ≅ (P ≫ L).functor)
    (N : Σ G : W ⟶ T, H.functor ≅ G.functor) :
    preReferenceNode F P η (preReferenceNode L Q ρ N) =
      preReferenceNode F (P ≫ Q) (η ≪≫ isoWhiskerLeft P.functor ρ) N := by
  rcases N with ⟨G, σ⟩
  have hf : (P ≫ Q ≫ G).functor = ((P ≫ Q) ≫ G).functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change η ≪≫ isoWhiskerLeft P.functor (ρ ≪≫ isoWhiskerLeft Q.functor σ) =
    (η ≪≫ isoWhiskerLeft P.functor ρ) ≪≫ isoWhiskerLeft (P ≫ Q).functor σ
  rw [isoWhiskerLeft_trans, Iso.trans_assoc]
  rfl

/-- The input's actual reference change is retained before fixed precomposition. -/
theorem pre_anchor_node (F : V ⟶ T) (P : V ⟶ W) {H L : W ⟶ T}
    (ρ : F.functor ≅ (P ≫ H).functor) (η : H.functor ≅ L.functor)
    (N : Σ G : W ⟶ T, L.functor ≅ G.functor) :
    preReferenceNode F P ρ (anchorNode η N) =
      preReferenceNode F P (ρ ≪≫ isoWhiskerLeft P.functor η) N := by
  rcases N with ⟨G, σ⟩
  apply congrArg (fun ν : F.functor ≅ (P ≫ G).functor ↦
    (⟨P ≫ G, ν⟩ : Σ G : V ⟶ T, F.functor ≅ G.functor))
  change ρ ≪≫ isoWhiskerLeft P.functor (η ≪≫ σ) = _
  rw [isoWhiskerLeft_trans, Iso.trans_assoc]

variable (F : V ⟶ T) (P : V ⟶ W) (H : W ⟶ T)
  (D : I → Σ G : W ⟶ T, H.functor ≅ G.functor)

/-- A full shared node determines the unchanged precomposed family through iso cancellation. -/
theorem pre_eq_of_node {ρ σ : F.functor ≅ (P ≫ H).functor} (j : I)
    (he : preReferenceNode F P ρ (D j) = preReferenceNode F P σ (D j)) (i : I) :
    preReferenceNode F P ρ (D i) = preReferenceNode F P σ (D i) := by
  have hs : (preReferenceNode F P ρ (D j)).2 = (preReferenceNode F P σ (D j)).2 :=
    eq_of_heq (Sigma.mk.inj he).2
  change ρ ≪≫ isoWhiskerLeft P.functor (D j).2 =
    σ ≪≫ isoWhiskerLeft P.functor (D j).2 at hs
  have hc := congrArg (fun ν ↦ ν ≪≫ (isoWhiskerLeft P.functor (D j).2).symm) hs
  have hρ : ρ = σ := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hc
  exact congrArg (fun η ↦ preReferenceNode F P η (D i)) hρ

theorem pre_families_match
    {N M : I → Σ G : V ⟶ T, F.functor ≅ G.functor}
    {ρ σ : F.functor ≅ (P ≫ H).functor}
    (hN : ∀ i, N i = preReferenceNode F P ρ (D i))
    (hM : ∀ i, M i = preReferenceNode F P σ (D i))
    (j : I) (he : N j = M j) (i : I) : N i = M i :=
  (hN i).trans ((pre_eq_of_node F P H D j
    ((hN j).symm.trans (he.trans (hM j))) i).trans (hM i).symm)

end Quillen.PerfectComplexes.BassH1Join
