/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexProductDiagram
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveWhiskering

/-!
# Full dependent reference nodes under product association

These algebraic identities retain both the actual model morphisms and complete reference
isomorphisms. They compare the literal product-composition references under precomposition,
postcomposition and association. No realized whole-nerve product comparison is asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceProduct

/-- Change only the reference isomorphism of a complete dependent node. -/
def reanchor {V W : Model.{u}} {F₀ F₁ : V ⟶ W}
    (η : F₀.functor ≅ F₁.functor) (N : CommonReferenceNerve.Node F₁) :
    CommonReferenceNerve.Node F₀ := ⟨N.1, η ≪≫ N.2⟩

/-- Original precomposition with its supplied complete target reference. -/
def preNode {V W T : Model.{u}} (F : V ⟶ T) (P : V ⟶ W) {H : W ⟶ T}
    (η : F.functor ≅ (P ≫ H).functor) (N : CommonReferenceNerve.Node H) :
    CommonReferenceNerve.Node F := reanchor η (CommonReferenceNerve.precompNode P N)

/-- Original postcomposition with its supplied complete target reference. -/
def postNode {V W T : Model.{u}} (F : V ⟶ T) (P : W ⟶ T) {H : V ⟶ W}
    (η : F.functor ≅ (H ≫ P).functor) (N : CommonReferenceNerve.Node H) :
    CommonReferenceNerve.Node F := reanchor η (CommonReferenceNerve.postcompNode P N)

private theorem pair_iso {V W T : Model.{u}} {H₀ H₁ : V ⟶ W} {G₀ G₁ : W ⟶ T}
    (e : H₀.functor ≅ H₁.functor) (f : G₀.functor ≅ G₁.functor) :
    (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso (e.prod f) =
      isoWhiskerRight e G₀.functor ≪≫ isoWhiskerLeft H₁.functor f := by
  apply Iso.ext
  rfl

private theorem pair_iso_other {V W T : Model.{u}} {H₀ H₁ : V ⟶ W} {G₀ G₁ : W ⟶ T}
    (e : H₀.functor ≅ H₁.functor) (f : G₀.functor ≅ G₁.functor) :
    (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso (e.prod f) =
      isoWhiskerLeft H₀.functor f ≪≫ isoWhiskerRight e G₁.functor := by
  apply Iso.ext
  ext X
  exact f.hom.naturality (e.hom.app X)

/-- Precomposition retains exactly the supplied reference transport. -/
theorem pre_node_reanchor {V W T : Model.{u}} (F : V ⟶ T)
    (P : V ⟶ W) (H : W ⟶ T) (η : F.functor ≅ (P ≫ H).functor)
    (N : CommonReferenceNerve.Node H) :
    preNode F P η N =
      reanchor η (preNode (P ≫ H) P (Iso.refl _) N) := by
  simp only [preNode, CommonReferenceNerve.precompNode, reanchor, Iso.refl_trans]

/-- Postcomposition retains exactly the supplied reference transport. -/
theorem post_node_reanchor {V W T : Model.{u}} (F : V ⟶ T)
    (H : V ⟶ W) (P : W ⟶ T) (η : F.functor ≅ (H ≫ P).functor)
    (N : CommonReferenceNerve.Node H) :
    postNode F P η N =
      reanchor η (postNode (H ≫ P) P (Iso.refl _) N) := by
  simp only [postNode, CommonReferenceNerve.postcompNode, reanchor, Iso.refl_trans]

/-- Compose the two actual full nodes with the literal composition-functor reference. -/
def node {V W T : Model.{u}} (F : V ⟶ T) (H : V ⟶ W) (G : W ⟶ T)
    (η : F.functor ≅ (H ≫ G).functor)
    (N : CommonReferenceNerve.Node H) (M : CommonReferenceNerve.Node G) :
    CommonReferenceNerve.Node F :=
  ⟨N.1 ≫ M.1, η ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso (N.2.prod M.2)⟩

/-- Transport in the first reference is the actual right-whiskered transport. -/
theorem node_first_reanchor {V W T : Model.{u}}
    (F : V ⟶ T) (H₀ H₁ : V ⟶ W) (G : W ⟶ T)
    (θ : H₀.functor ≅ H₁.functor) (η : F.functor ≅ (H₀ ≫ G).functor)
    (N : CommonReferenceNerve.Node H₁) (M : CommonReferenceNerve.Node G) :
    node F H₀ G η (reanchor θ N) M =
      node F H₁ G (η ≪≫ isoWhiskerRight θ G.functor) N M := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [node, reanchor, pair_iso,
    isoWhiskerRight_trans, Iso.trans_assoc]

/-- Transport in the second reference is the actual left-whiskered transport. -/
theorem node_second_reanchor {V W T : Model.{u}}
    (F : V ⟶ T) (H : V ⟶ W) (G₀ G₁ : W ⟶ T)
    (θ : G₀.functor ≅ G₁.functor) (η : F.functor ≅ (H ≫ G₀).functor)
    (N : CommonReferenceNerve.Node H) (M : CommonReferenceNerve.Node G₁) :
    node F H G₀ η N (reanchor θ M) =
      node F H G₁ (η ≪≫ isoWhiskerLeft H.functor θ) N M := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [node, reanchor, pair_iso_other,
    isoWhiskerLeft_trans, Iso.trans_assoc]

/-- Full product nodes commute with fixed original precomposition. -/
theorem node_precomp {V V' W T : Model.{u}}
    (F : V ⟶ T) (P : V ⟶ V') (H : V' ⟶ W) (G : W ⟶ T)
    (η : F.functor ≅ ((P ≫ H) ≫ G).functor)
    (N : CommonReferenceNerve.Node H) (M : CommonReferenceNerve.Node G) :
    node F (P ≫ H) G η (preNode (P ≫ H) P (Iso.refl _) N) M =
      preNode F P η (node (H ≫ G) H G (Iso.refl _) N M) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp only [node, preNode, reanchor, CommonReferenceNerve.precompNode, pair_iso,
    Iso.trans_hom, Iso.refl_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.id_comp]
  rfl

/-- Full product nodes commute with fixed original postcomposition. -/
theorem node_postcomp {V W T T' : Model.{u}}
    (F : V ⟶ T') (H : V ⟶ W) (G : W ⟶ T) (J : T ⟶ T')
    (η : F.functor ≅ (H ≫ (G ≫ J)).functor)
    (N : CommonReferenceNerve.Node H) (M : CommonReferenceNerve.Node G) :
    node F H (G ≫ J) η N (postNode (G ≫ J) J (Iso.refl _) M) =
      postNode F J η (node (H ≫ G) H G (Iso.refl _) N M) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp only [node, postNode, reanchor, CommonReferenceNerve.postcompNode, pair_iso,
    Iso.trans_hom, Iso.refl_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.map_comp, Category.id_comp]
  rfl

/-- The two product associations retain the same complete dependent node. -/
theorem node_associativity {V W W' T : Model.{u}}
    (F : V ⟶ T) (H : V ⟶ W) (J : W ⟶ W') (G : W' ⟶ T)
    (η : F.functor ≅ ((H ≫ J) ≫ G).functor)
    (N : CommonReferenceNerve.Node H) (M : CommonReferenceNerve.Node G) :
    node F (H ≫ J) G η (postNode (H ≫ J) J (Iso.refl _) N) M =
      node F H (J ≫ G) η N (preNode (J ≫ G) J (Iso.refl _) M) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp only [node, postNode, preNode, reanchor,
    CommonReferenceNerve.postcompNode, CommonReferenceNerve.precompNode, pair_iso,
    Iso.trans_hom, Iso.refl_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.id_comp]
  rfl

end Quillen.Waldhausen.IteratedS.CommonReferenceProduct
