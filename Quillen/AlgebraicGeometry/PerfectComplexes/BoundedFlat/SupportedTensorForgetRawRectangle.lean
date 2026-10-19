/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedEvaluationForget
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationForgetModel

/-! # The actual tensor and support-forgetting evaluation rectangle

The two routes use the original supported and ambient tensor evaluation transitions and the
actual full-subcategory inclusion. Their complete raw rectangle commutes by the original
underlying transformation equality, before any selected-zero normalization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation

variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

/-- The genuine supported section pullback/forgetting square is strict before evaluation. -/
theorem forgetReindexInputSquare :
    (supportedPairModelMap p).functor ⋙ (supportedForget (X := op A.obj.right) A.obj.hom).functor =
      (supportedForget (X := op B.obj.right) B.obj.hom).functor ⋙
        (globalModel.map p.hom.right.op).functor :=
  supportedPairReindex_forget p

/-- Both complete raw tensor evaluation routes preserve the actual support-forgetting square. -/
theorem tensorForgetRawRectangle_hom :
    whiskerLeft (supportedEvaluation (X := op B.obj.right) B.obj.hom)
        (tensorSupportedPairForgetIso p).hom ≫
        (isoSquareRoute (evaluationForgetIso (X := op B.obj.right) B.obj.hom)
          (GlobalSectionChangeIndex.tensorEvaluationIso p.hom.right).symm).inv =
      (isoSquareRoute (tensorEvaluationIso p).symm
        (evaluationForgetIso (X := op A.obj.right) A.obj.hom)).inv ≫
        eqToHom (congrArg (fun F => F ⋙ globalEvaluation (op A.obj.right))
          (forgetReindexInputSquare p)) := by
  apply NatTrans.ext
  funext K
  change (supported (X := op B.obj.right) B.obj.hom).FullSubcategory at K
  simp only [isoSquareRoute, Iso.trans_inv, Iso.symm_inv,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app,
    tensorSupportedPairForgetIso, evaluationForgetIso, supportedForget, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Iso.refl_hom, Iso.refl_inv,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  change (boundedFlatPerfectTensorUnitPullback p.hom.right).map
      (𝟙 ((globalEvaluation (op B.obj.right)).obj K.obj)) ≫
        (GlobalSectionChangeIndex.tensorEvaluationIso p.hom.right).hom.app K.obj =
    (tensorCoefficientSupportedForget A.obj.hom).map
        ((tensorEvaluationIso p).hom.app K) ≫
      𝟙 ((globalEvaluation (op A.obj.right)).obj
        ((globalModel.map p.hom.right.op).functor.obj K.obj))
  calc
    _ = (GlobalSectionChangeIndex.tensorEvaluationIso p.hom.right).hom.app K.obj :=
      (congrArg (fun k => k ≫
        (GlobalSectionChangeIndex.tensorEvaluationIso p.hom.right).hom.app K.obj)
        ((boundedFlatPerfectTensorUnitPullback p.hom.right).map_id _)).trans
          (Category.id_comp _)
    _ = _ := (GlobalSectionChangeIndex.tensorEvaluationIso_forget_hom_app p K).symm.trans
      (Category.comp_id _).symm

end Quillen.PerfectComplexes.SupportedTensorEvaluation
