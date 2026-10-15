/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MVertexWholeNative

/-! Full reference-row transport for the actual outer M joins. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH0Merge
open Quillen.PerfectComplexes.BassH1Join

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join
variable {V W T : Model.{u}} {I : Type v}

/-- Reanchoring an actual precomposed family preserves the original reference association. -/
theorem anchor_pre_node {F K : V ⟶ T} (P : V ⟶ W) {H : W ⟶ T}
    (η : F.functor ≅ K.functor) (ρ : K.functor ≅ (P ≫ H).functor)
    (N : Σ G : W ⟶ T, H.functor ≅ G.functor) :
    anchorNode η (preReferenceNode K P ρ N) =
      preReferenceNode F P (η ≪≫ ρ) N := by
  rcases N with ⟨G, σ⟩
  exact congrArg (fun ν : F.functor ≅ (P ≫ G).functor ↦
    (⟨P ≫ G, ν⟩ : Σ G : V ⟶ T, F.functor ≅ G.functor)) (Iso.trans_assoc η ρ _).symm

/-- Equal actual precomposition maps and one full reference node determine the whole native row. -/
theorem pre_families_match_maps
    (F : V ⟶ T) (P P' : V ⟶ W) (H : W ⟶ T) (heP : P = P')
    (D : I → Σ G : W ⟶ T, H.functor ≅ G.functor)
    {N M : I → Σ G : V ⟶ T, F.functor ≅ G.functor}
    {ρ : F.functor ≅ (P ≫ H).functor} {σ : F.functor ≅ (P' ≫ H).functor}
    (hN : ∀ i, N i = preReferenceNode F P ρ (D i))
    (hM : ∀ i, M i = preReferenceNode F P' σ (D i))
    (j : I) (he : N j = M j) (i : I) : N i = M i := by
  subst P'
  exact pre_families_match F P H D hN hM j he i

/-- Actual equality anchors compose on a complete original binary target node. -/
theorem anchor_binary_target_node {X Y Z : Scheme.{u}}
    (F K : modelOf (boundedFlatPerfectWaldhausen Z) ⟶
      modelOf (boundedFlatPerfectWaldhausen X)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : F.functor = K.functor)
    (h : K.functor = (BinaryNormalizationSimplex.sourceMap f g).functor) :
    anchorNode (eqToIso e) (binaryTargetNode K f g h) =
      binaryTargetNode F f g (e.trans h) := by
  refine Sigma.ext (show BinaryNormalizationSimplex.targetMap f g =
    BinaryNormalizationSimplex.targetMap f g from rfl) ?_
  apply heq_of_eq
  change eqToIso e ≪≫ (eqToIso h ≪≫ BinaryNormalizationSimplex.total f g) =
    eqToIso (e.trans h) ≪≫ BinaryNormalizationSimplex.total f g
  rw [← Iso.trans_assoc, eqToIso_trans]

end Quillen.PerfectComplexes.BassMOuterJoin
