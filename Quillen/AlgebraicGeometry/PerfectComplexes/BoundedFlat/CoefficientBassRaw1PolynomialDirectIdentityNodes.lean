/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPolynomialSheetNormalization
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNodeTransport

/-! Full identity-source node cancellation for the two actual direct chart actions. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialDirectIdentityNodes
open CommonReferenceNerve

/-- Whole normalization of an identity-source moving node keeps its complete terminal anchor. -/
theorem normalize_identity_node {V W T : Model.{u}} (F M : V ⟶ W) (J : W ⟶ T)
    (H G : V ⟶ T) (η : F.functor ≅ M.functor)
    (θ : G.functor ≅ ((𝟙 V) ≫ H).functor)
    (ρ : H.functor ≅ (M ≫ J).functor) (N : Node H) :
    CommonReferenceProduct.reanchor (F₀ := F ≫ J) (F₁ := G)
      (isoWhiskerRight (η ≪≫ (Functor.leftUnitor M.functor).symm) J.functor ≪≫
        (θ ≪≫ isoWhiskerLeft (𝟙 V : V ⟶ V).functor ρ ≪≫
          (Functor.associator (𝟙 V : V ⟶ V).functor M.functor J.functor).symm).symm)
      (⟨(𝟙 V) ≫ N.1, θ ≪≫ isoWhiskerLeft (𝟙 V : V ⟶ V).functor N.2 ≪≫
        isoWhiskerRight (Iso.refl (𝟙 V : V ⟶ V).functor) N.1.functor⟩ : Node G) =
    CommonReferenceProduct.reanchor (F₀ := F ≫ J) (F₁ := H)
      (isoWhiskerRight η J.functor ≪≫ ρ.symm) N := by
  dsimp only [CommonReferenceProduct.reanchor]
  apply Sigma.ext
  · exact Category.id_comp N.1
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp only [Iso.trans_symm, Iso.symm_symm_eq, isoWhiskerRight_trans, Iso.trans_assoc,
    isoWhiskerRight_refl, Iso.trans_refl, Iso.symm_self_id_assoc, Iso.trans_hom,
    isoWhiskerRight_hom, Iso.symm_hom, isoWhiskerLeft_inv, isoWhiskerLeft_hom,
    NatTrans.comp_app, comp_obj, whiskerRight_app, id_obj, leftUnitor_inv_app,
    CategoryTheory.Functor.map_id, associator_hom_app, whiskerLeft_app, Category.id_comp]
  change J.functor.map (η.hom.app X) ≫ 𝟙 _ ≫ ρ.inv.app X ≫ N.2.hom.app X = _
  simp only [Category.id_comp]

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialDirectIdentityNodes
