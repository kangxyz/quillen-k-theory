/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputPolynomialNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputPolynomialPlacement

/-! The complete Laurent baseline joins the central cap at the fourth source-square node. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
open BassH0Merge CommonReferenceNerve CommonReferenceProduct

private theorem laurent_word {U V W T Y Z : Type u}
    [Category.{v} U] [Category.{v} V] [Category.{v} W]
    [Category.{v} T] [Category.{v} Y] [Category.{v} Z]
    (H : U ⥤ V) (B : V ⥤ W) (F : W ⥤ T) (E : V ⥤ Y)
    (J : Y ⥤ T) (K : T ⥤ Z) (L : Y ⥤ Z) (D : U ⥤ W) (X : U ⥤ Y)
    (a : X ⋙ J ≅ D ⋙ F) (rho : D ≅ H ⋙ B) (delta : X ≅ H ⋙ E)
    (b : E ⋙ J ≅ B ⋙ F) (tau : L ≅ J ⋙ K)
    (h : a ≪≫ isoWhiskerRight rho F = isoWhiskerRight delta J ≪≫
      Functor.associator H E J ≪≫ isoWhiskerLeft H b ≪≫
      (Functor.associator H B F).symm) :
    isoWhiskerLeft X tau ≪≫ (Functor.associator X J K).symm ≪≫
      isoWhiskerRight a K ≪≫ Functor.associator D F K ≪≫
      isoWhiskerRight rho (F ⋙ K) =
    isoWhiskerRight delta L ≪≫ Functor.associator H E L ≪≫
      isoWhiskerLeft H (isoWhiskerLeft E tau ≪≫ isoWhiskerRight b K) ≪≫
      (Functor.associator H B (F ⋙ K)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  have hx := congrArg (fun e ↦ e.hom.app x) h
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom, Category.id_comp, Category.comp_id] at hx ⊢
  erw [Category.comp_id]
  simp only [Functor.comp_map]
  rw [← K.map_comp, hx, K.map_comp]
  simpa only [Category.assoc, Functor.comp_map, Functor.comp_obj] using
    congrArg (fun f ↦ f ≫ K.map (b.hom.app (H.obj x)))
      (tau.hom.naturality (delta.hom.app x)).symm

private theorem model_comp {U V W : Model.{u}} (F : U ⟶ V) (G : V ⟶ W) :
    (F ≫ G).functor = F.functor ⋙ G.functor := rfl

private theorem reanchor_product {U V W : Model.{u}} (D : U ⟶ V) (F : V ⟶ W)
    (X Y : U ⟶ W) (a : X.functor ≅ Y.functor) (b : Y.functor ≅ (D ≫ F).functor)
    (N : Node D) (M : Node F) :
    reanchor a (node Y D F b N M) =
      reanchor (a ≪≫ b) (node (D ≫ F) D F (Iso.refl _) N M) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [reanchor, node, Iso.refl_trans, Iso.trans_assoc]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hd : coefficientMap P (β.app d) ≫ polynomialProjection P d = laurentProjection P d)

/-- The original chart endpoint intertwines the full polynomial node-four transport. -/
theorem laurent_anchor_node4 :
    laurentAnchor P p q w β hd ≪≫ Functor.associator
      (sourceReference P p).functor (pairReference P q w).functor
      (BassMWholeNerve.coefficientModel P (β.app d)).functor ≪≫
      isoWhiskerRight (rightSquareIso P p)
        (pairReference P q w ≫ BassMWholeNerve.coefficientModel P (β.app d)).functor =
    isoWhiskerRight (TripleLaurent.inputIso P p q w)
      (BassProjectionPath.source P d).functor ≪≫ Functor.associator
        (normalizedMap (coefficientMap P p)).functor (inputReference P q w).functor
        (BassProjectionPath.source P d).functor ≪≫
      isoWhiskerLeft (normalizedMap (coefficientMap P p)).functor
        (PairProjection.laurentIso P q w β hd) ≪≫
      (Functor.associator (normalizedMap (coefficientMap P p)).functor
        (normalizedMap (polynomialProjection P b)).functor
        (pairReference P q w ≫ BassMWholeNerve.coefficientModel P (β.app d)).functor).symm := by
  rw [PairProjection.laurentIso_chart]
  have h := laurent_word (normalizedMap (coefficientMap P p)).functor
    (normalizedMap (polynomialProjection P b)).functor (pairReference P q w).functor
    (inputReference P q w).functor (normalizedMap (polynomialProjection P d)).functor
    (BassMWholeNerve.coefficientModel P (β.app d)).functor
    (BassProjectionPath.source P d).functor (sourceReference P p).functor
    (input P p q w).functor (polynomialAnchor P p q w) (rightSquareIso P p)
    (TripleLaurent.inputIso P p q w) (PairLowerReference.polynomialAnchor P q w)
    (BassMJoin.projectionEndpointIso P β hd) (polynomial_anchor_node4 P p q w)
  simpa only [laurentAnchor, PairLowerReference.chartAnchor, targetProjection,
    BassProjectionPath.WholeReference.reference, model_comp, Iso.trans_assoc] using h

/-- Every Laurent node, not only attached polynomial nodes, has the same central reference. -/
theorem laurent_node4
    (M : Node (pairReference P q w ≫ BassMWholeNerve.coefficientModel P (β.app d))) :
    reanchor (laurentAnchor P p q w β hd)
      (FiniteSourceSheet.laurentNode (sourceReference P p) (pairReference P q w)
        (BassMWholeNerve.coefficientModel P (β.app d))
        (CoefficientSquareFamilies.polynomialNodes P p) M 4) =
    reanchor (isoWhiskerRight (TripleLaurent.inputIso P p q w)
      (BassProjectionPath.source P d).functor)
      (precompNode (normalizedMap (coefficientMap P p))
        (PairProjection.laurentNode P q w β hd M)) := by
  unfold FiniteSourceSheet.laurentNode
  rw [source_node4, reanchor_product]
  have h := source_node_transport (normalizedMap (coefficientMap P p))
    (normalizedMap (polynomialProjection P b))
    (pairReference P q w ≫ BassMWholeNerve.coefficientModel P (β.app d))
    (inputReference P q w) (BassProjectionPath.source P d) (sourceReference P p)
    (BassProjectionPath.WholeReference.reference P d (input P p q w))
    (laurentAnchor P p q w β hd ≪≫ Functor.associator (sourceReference P p).functor
      (pairReference P q w).functor (BassMWholeNerve.coefficientModel P (β.app d)).functor)
    (rightSquareIso P p)
    (isoWhiskerRight (TripleLaurent.inputIso P p q w) (BassProjectionPath.source P d).functor)
    (PairProjection.laurentIso P q w β hd)
    (by simpa only [Iso.trans_assoc] using laurent_anchor_node4 P p q w β hd) M
  simpa only [PairProjection.laurentNode] using h

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
