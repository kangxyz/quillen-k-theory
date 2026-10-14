/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1MiddleJoinReference

/-! Full original reference families under both fixed whiskerings, with endpoint cancellation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes.BassH1Join
variable {V₀ W₀ V W : Model.{u}} {I : Type v}
  (F : V ⟶ W) (P : V ⟶ V₀) (J : W₀ ⟶ W) (H : V₀ ⟶ W₀)
  (D : I → Σ G : V₀ ⟶ W₀, H.functor ≅ G.functor)

/-- Both fixed original maps are retained around every full input reference node. -/
def prePostNodes (ρ : F.functor ≅ (P ≫ H ≫ J).functor) (i : I) :
    Σ G : V ⟶ W, F.functor ≅ G.functor :=
  ⟨P ≫ (D i).1 ≫ J, ρ ≪≫ isoWhiskerLeft P.functor (isoWhiskerRight (D i).2 J.functor)⟩

/-- Literal interchange of the two fixed functor whiskerings. -/
theorem whisker_iso_interchange {G : V₀ ⟶ W₀} (ν : H.functor ≅ G.functor) :
    isoWhiskerRight (isoWhiskerLeft P.functor ν) J.functor =
      isoWhiskerLeft P.functor (isoWhiskerRight ν J.functor) := by
  apply Iso.ext
  ext X
  rfl

/-- Postcompose an original precomposed node; only its genuine reference association changes. -/
theorem post_pre_node {K : V ⟶ W₀}
    (ρ : K.functor ≅ (P ≫ H).functor) (η : F.functor ≅ (K ≫ J).functor) (i : I) :
    postReferenceNode F J η (BassH0Merge.preReferenceNode K P ρ (D i)) =
      prePostNodes F P J H D (η ≪≫ isoWhiskerRight ρ J.functor) i := by
  have hF : ((P ≫ (D i).1) ≫ J).functor = (P ≫ (D i).1 ≫ J).functor := rfl
  apply Sigma.ext (Model.Hom.ext hF)
  apply heq_of_eq
  change η ≪≫ isoWhiskerRight (ρ ≪≫ isoWhiskerLeft P.functor (D i).2) J.functor =
    (η ≪≫ isoWhiskerRight ρ J.functor) ≪≫
      isoWhiskerLeft P.functor (isoWhiskerRight (D i).2 J.functor)
  rw [isoWhiskerRight_trans, whisker_iso_interchange, Iso.trans_assoc]

/-- Precompose an original postcomposed node with the same two actual fixed maps. -/
theorem pre_post_node {K : V₀ ⟶ W}
    (ρ : K.functor ≅ (H ≫ J).functor) (η : F.functor ≅ (P ≫ K).functor) (i : I) :
    BassH0Merge.preReferenceNode F P η (postReferenceNode K J ρ (D i)) =
      prePostNodes F P J H D (η ≪≫ isoWhiskerLeft P.functor ρ) i := by
  have hF : (P ≫ (D i).1 ≫ J).functor = (P ≫ (D i).1 ≫ J).functor := rfl
  apply Sigma.ext (Model.Hom.ext hF)
  apply heq_of_eq
  change η ≪≫ isoWhiskerLeft P.functor (ρ ≪≫ isoWhiskerRight (D i).2 J.functor) =
    (η ≪≫ isoWhiskerLeft P.functor ρ) ≪≫
      isoWhiskerLeft P.functor (isoWhiskerRight (D i).2 J.functor)
  rw [isoWhiskerLeft_trans, Iso.trans_assoc]

/-- A full shared node determines this fixed reference family by iso cancellation. -/
theorem prePost_eq_of_node
    {ρ σ : F.functor ≅ (P ≫ H ≫ J).functor} (j : I)
    (he : prePostNodes F P J H D ρ j = prePostNodes F P J H D σ j) (i : I) :
    prePostNodes F P J H D ρ i = prePostNodes F P J H D σ i := by
  have hs : (prePostNodes F P J H D ρ j).2 = (prePostNodes F P J H D σ j).2 :=
    eq_of_heq (Sigma.mk.inj he).2
  change ρ ≪≫ isoWhiskerLeft P.functor (isoWhiskerRight (D j).2 J.functor) =
    σ ≪≫ isoWhiskerLeft P.functor (isoWhiskerRight (D j).2 J.functor) at hs
  have hc := congrArg
    (fun η ↦ η ≪≫ (isoWhiskerLeft P.functor (isoWhiskerRight (D j).2 J.functor)).symm) hs
  have hρ : ρ = σ := by simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hc
  exact congrArg (fun η ↦ prePostNodes F P J H D η i) hρ

/-- Two actual row representations with one full shared node retain every member of the family. -/
theorem prePost_families_match
    {N M : I → Σ G : V ⟶ W, F.functor ≅ G.functor}
    {ρ σ : F.functor ≅ (P ≫ H ≫ J).functor}
    (hN : ∀ i, N i = prePostNodes F P J H D ρ i)
    (hM : ∀ i, M i = prePostNodes F P J H D σ i)
    (j : I) (he : N j = M j) (i : I) : N i = M i :=
  (hN i).trans ((prePost_eq_of_node F P J H D j
    ((hN j).symm.trans (he.trans (hM j))) i).trans (hM i).symm)

end Quillen.PerfectComplexes.BassH1Join
