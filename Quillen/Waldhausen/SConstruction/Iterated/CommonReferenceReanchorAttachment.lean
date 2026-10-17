/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceProductNodes
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveReanchorFamily
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily

/-! Exact full-reference reanchoring commutes with attachment on the entire nerve parameter. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve
variable {V W T : Model.{u}} (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)

/-- Compose the actual attachment reference, keeping its complete dependent node. -/
theorem reanchor_attach_node (τ : G.functor ≅ G.functor)
    (ε : G.functor ≅ (F ≫ J).functor) (N : Node F) :
    CommonReferenceProduct.reanchor τ (attachPostcompNode F J G ε N) =
      attachPostcompNode F J G (τ ≪≫ ε) N := by
  rcases N with ⟨K, ρ⟩
  change (⟨K ≫ J, τ ≪≫ (ε ≪≫ isoWhiskerRight ρ J.functor)⟩ : Node G) =
    ⟨K ≫ J, (τ ≪≫ ε) ≪≫ isoWhiskerRight ρ J.functor⟩
  exact congrArg (fun η : G.functor ≅ (K ≫ J).functor ↦ (⟨K ≫ J, η⟩ : Node G))
    (Iso.trans_assoc τ ε (isoWhiskerRight ρ J.functor)).symm

/-- The same reference identity holds at every point, not just vertices or endpoints. -/
theorem reanchor_attach_parameter (τ : G.functor ≅ G.functor)
    (ε : G.functor ≅ (F ≫ J).functor) (y : |nerve (Codiscrete (Node F))|) :
    mapParameter (CommonReferenceProduct.reanchor τ)
      (mapParameter (attachPostcompNode F J G ε) y) =
        mapParameter (attachPostcompNode F J G (τ ≪≫ ε)) y := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F y
  rw [← hz, mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns : Fin (k + 1) → Node G ↦ parameter G ns z)
    (funext fun i ↦ reanchor_attach_node F J G τ ε (N i))

/-- Reanchoring preserves native evaluation on the entire realization, including degree zero. -/
theorem pointwise_reanchor {V W : Model.{u}} {F G : V ⟶ W}
    (τ : F.functor ≅ G.functor) (n : ℕ) (y : |nerve (Codiscrete (Node G))|)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily F n (mapParameter (CommonReferenceProduct.reanchor τ) y) x =
      pointwisePrespectrumFamily G n y x := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter G y
  rw [← hz, mapParameter_parameter, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact congrArg (fun f ↦ f (z, x)) (prespectrumFamily_reanchor τ N n)

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve
