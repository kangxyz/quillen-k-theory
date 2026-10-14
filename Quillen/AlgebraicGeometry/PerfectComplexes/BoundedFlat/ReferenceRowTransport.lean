/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BinaryRowEndpoint

/-! Full dependent reference transport of a precomposed source node. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
variable {V W T : Model.{u}} (F : V ⟶ T) (P : V ⟶ W)

/-- The literal precomposition/reanchoring operation on full reference nodes. -/
def preReferenceNode {H : W ⟶ T} (ρ : F.functor ≅ (P ≫ H).functor)
    (N : Σ G : W ⟶ T, H.functor ≅ G.functor) :
    Σ G : V ⟶ T, F.functor ≅ G.functor :=
  ⟨P ≫ N.1, ρ ≪≫ isoWhiskerLeft P.functor N.2⟩

/-- Reanchoring an original source node retains its exact supplied reference. -/
theorem preReferenceNode_source {H : W ⟶ T} (ρ : F.functor ≅ (P ≫ H).functor) :
    preReferenceNode F P ρ ⟨H, Iso.refl _⟩ = ⟨P ≫ H, ρ⟩ := by
  unfold preReferenceNode
  dsimp only
  rw [isoWhiskerLeft_refl]
  exact congrArg (fun η : F.functor ≅ (P ≫ H).functor ↦
    (⟨P ≫ H, η⟩ : Σ G : V ⟶ T, F.functor ≅ G.functor)) (Iso.trans_refl ρ)

/-- An actual functor equality transports the full source node, including its original reference. -/
theorem preReferenceNode_source_transport {H H' : W ⟶ T} (e : H.functor = H'.functor)
    (ρ : F.functor ≅ (P ≫ H).functor) :
    (⟨P ≫ H, ρ⟩ : Σ G : V ⟶ T, F.functor ≅ G.functor) =
      ⟨P ≫ H', ρ ≪≫ isoWhiskerLeft P.functor (eqToIso e)⟩ := by
  have hH : H = H' := Model.Hom.ext e
  subst H'
  change (⟨P ≫ H, ρ⟩ : Σ G : V ⟶ T, F.functor ≅ G.functor) =
    ⟨P ≫ H, ρ ≪≫ isoWhiskerLeft P.functor (eqToIso rfl)⟩
  rw [eqToIso_refl, isoWhiskerLeft_refl]
  exact congrArg (fun η : F.functor ≅ (P ≫ H).functor ↦
    (⟨P ≫ H, η⟩ : Σ G : V ⟶ T, F.functor ≅ G.functor)) (Iso.trans_refl ρ).symm

/-- Reanchor a single full node without unfolding any original geometric definition. -/
def anchorNode {V W : Model.{u}} {F₀ F₁ : V ⟶ W} (ρ : F₀.functor ≅ F₁.functor)
    (N : Σ G : V ⟶ W, F₁.functor ≅ G.functor) : Σ G : V ⟶ W, F₀.functor ≅ G.functor :=
  ⟨N.1, ρ ≪≫ N.2⟩

theorem anchorNode_congr {V W : Model.{u}} {F₀ F₁ : V ⟶ W}
    (ρ : F₀.functor ≅ F₁.functor) {N M : Σ G : V ⟶ W, F₁.functor ≅ G.functor}
    (h : N = M) : anchorNode ρ N = anchorNode ρ M := congrArg (anchorNode ρ) h

theorem anchorNode_assoc {V W : Model.{u}} {F₀ F₁ F₂ : V ⟶ W}
    (ρ : F₀.functor ≅ F₁.functor) (σ : F₁.functor ≅ F₂.functor)
    (N : Σ G : V ⟶ W, F₂.functor ≅ G.functor) :
    anchorNode ρ (anchorNode σ N) = anchorNode (ρ ≪≫ σ) N :=
  congrArg (fun η : F₀.functor ≅ N.1.functor ↦
    (⟨N.1, η⟩ : Σ G : V ⟶ W, F₀.functor ≅ G.functor)) (Iso.trans_assoc ρ σ N.2).symm

end Quillen.PerfectComplexes.BassH0Merge
