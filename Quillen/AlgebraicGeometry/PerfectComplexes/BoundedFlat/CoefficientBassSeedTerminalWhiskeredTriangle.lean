/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalProjectionTriangle

/-! The actual projection attachment retains its complete source-reference whiskering. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalWhiskeredTriangle

private theorem whiskered_anchor {V A B B' C D : Model.{u}}
    (E : V ⟶ A) (F : A ⟶ B) (G : A ⟶ C) (J : B ⟶ C)
    (L : C ⟶ D) (H : B ⟶ D) (M : B ⟶ B') (K : B' ⟶ D)
    (e : G.functor ≅ (F ≫ J).functor)
    (l : H.functor ≅ (J ≫ L).functor)
    (r : H.functor ≅ (M ≫ K).functor)
    (k : (G ≫ L).functor ≅ ((F ≫ M) ≫ K).functor)
    (hk : isoWhiskerRight e L.functor ≪≫
      Functor.associator F.functor J.functor L.functor ≪≫
      isoWhiskerLeft F.functor l.symm ≪≫ isoWhiskerLeft F.functor r ≪≫
      (Functor.associator F.functor M.functor K.functor).symm = k) :
    isoWhiskerRight (isoWhiskerLeft E.functor e) L.functor ≪≫
      Functor.associator (E ≫ F).functor J.functor L.functor ≪≫
      isoWhiskerLeft (E ≫ F).functor l.symm ≪≫
      isoWhiskerLeft (E ≫ F).functor r ≪≫
      (Functor.associator (E ≫ F).functor M.functor K.functor).symm =
    Functor.associator E.functor G.functor L.functor ≪≫
      isoWhiskerLeft E.functor k ≪≫
      (Functor.associator E.functor (F ≫ M).functor K.functor).symm ≪≫
      isoWhiskerRight (Functor.associator E.functor F.functor M.functor).symm K.functor := by
  rw [← hk]
  apply Iso.ext
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app]
  dsimp
  simp only [Category.assoc]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id] | erw [K.functor.map_id]
  rfl

open BassH0Merge CoefficientBassSeedTargetChartAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))

/-- The whole projection triangle remains valid on every node of the actual input reference. -/
theorem target_anchor_whisker :
    targetAnchor P f (E ≫ normalizedMap (polynomialProjection P a))
      (E ≫ BassProjectionPath.source P a)
      (isoWhiskerLeft E.functor
        (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P a))) =
    Functor.associator E.functor (BassProjectionPath.source P a).functor (L P f).functor ≪≫
      isoWhiskerLeft E.functor
        (CoefficientBassSeedTerminalProjectionTriangle.projectionAnchor P f) ≪≫
      (Functor.associator E.functor
        (normalizedMap (polynomialProjection P a) ≫ M P f).functor (Jb P (b := b)).functor).symm ≪≫
      isoWhiskerRight
        (Functor.associator E.functor (normalizedMap (polynomialProjection P a)).functor
          (M P f).functor).symm (Jb P (b := b)).functor := by
  have h := whiskered_anchor E (normalizedMap (polynomialProjection P a))
    (BassProjectionPath.source P a) (Ja P (a := a)) (L P f) (H P f) (M P f)
    (Jb P (b := b))
    (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P a))
    (leftIso P f) (rightIso P f)
    (CoefficientBassSeedTerminalProjectionTriangle.projectionAnchor P f)
    (by simpa only [targetAnchor, squareAnchor, Iso.trans_assoc] using
      (CoefficientBassSeedTerminalProjectionTriangle.target_anchor P f))
  simpa only [targetAnchor, squareAnchor, Iso.trans_assoc] using h

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalWhiskeredTriangle
