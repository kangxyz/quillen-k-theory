/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedCarrierAugmentationCells
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! Full ordinary and shifted attachment references commute with actual source precomposition. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open scoped Simplicial Topology
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenPrecomp
variable {U V W T : Model.{u}} (A : U ⟶ V) (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)

/-- Precomposition retains the full original anchor and its explicit associativity transport. -/
def anchor (ε : G.functor ≅ (F ≫ J).functor) :
    (A ≫ G).functor ≅ ((A ≫ F) ≫ J).functor :=
  isoWhiskerLeft A.functor ε ≪≫ (Functor.associator A.functor F.functor J.functor).symm

/-- The entire dependent attachment node commutes, including its reference isomorphism. -/
theorem attachment_node (ε : G.functor ≅ (F ≫ J).functor) (N : Node F) :
    precompNode A (attachPostcompNode F J G ε N) =
      attachPostcompNode (A ≫ F) J (A ≫ G) (anchor A F J G ε) (precompNode A N) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  simp only [precompNode, attachPostcompNode, anchor, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Iso.symm_hom, Functor.associator_inv_app, Functor.comp_obj,
    Category.assoc]
  exact congrArg (fun f ↦ ε.hom.app (A.functor.obj X) ≫ f)
    (Category.id_comp (J.functor.map (N.2.hom.app (A.functor.obj X)))).symm

/-- Forward inner-unit shifts are preserved, without postulating a polynomial unit lift. -/
theorem shifted_anchor (τ : G.functor ≅ G.functor)
    (ε : G.functor ≅ (F ≫ J).functor) :
    anchor A F J G (τ ≪≫ ε) = isoWhiskerLeft A.functor τ ≪≫ anchor A F J G ε := by
  apply Iso.ext
  ext X
  simp [anchor]

/-- The full simplicial attachment square, used for both of the original sheets. -/
theorem attachment_simplicial (ε : G.functor ≅ (F ≫ J).functor) :
    CutOpenCarrier.attaching F J G ε ≫ nerveMap (Codiscrete.functorOfFun (precompNode A)) =
      nerveMap (Codiscrete.functorOfFun (precompNode A)) ≫
        CutOpenCarrier.attaching (A ≫ F) J (A ≫ G) (anchor A F J G ε) := by
  have h : (fun N : Node F ↦ precompNode A (attachPostcompNode F J G ε N)) =
      (fun N : Node F ↦
        attachPostcompNode (A ≫ F) J (A ≫ G) (anchor A F J G ε) (precompNode A N)) :=
    funext (attachment_node A F J G ε)
  exact congrArg (fun f ↦ nerveMap (Codiscrete.functorOfFun f)) h

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenPrecomp
