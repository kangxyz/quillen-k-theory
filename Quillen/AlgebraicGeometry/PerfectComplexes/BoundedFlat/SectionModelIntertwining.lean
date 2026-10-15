/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelCoherence

/-!
# Evaluation intertwining through the original normalized models

An actual section transformation intertwined by the original coefficient transition remains
intertwined after the unchanged geometric normalization and common-universe lift.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

private theorem coefficientIso_hom_app
    {R S : CommRingCat.{u}} (f : R ⟶ S) (s : BoundedFlatAffineSections R) :
    (boundedFlatAffineSectionEvaluationCoefficientIso (R := R) (S := S) f).hom.app s =
    (AsSmall.up : BoundedFlatPerfect (Spec S) ⥤
      SmallModel (BoundedFlatPerfect (Spec S))).map
      ((boundedFlatAffineSectionCoefficientIso (R := R) (S := S) f).hom.app s ≫
        (boundedFlatPullbackNormalizationIso (Spec.map f)).hom.app
          ((boundedFlatAffineOriginalEvaluation R).obj s)) := by
  rw [boundedFlatAffineSectionEvaluationCoefficientIso_hom_app]
  simp only [Quillen.CategoryTheory.GrothendieckSections.normalizedCoefficientIso,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    ← boundedFlatAffineSectionCoefficientIso_eq]
  rfl

private def evaluationDown (R : CommRingCat.{u}) :
    modelOf (boundedFlatPerfectWaldhausen (Spec R)) ⥤ BoundedFlatPerfect (Spec R) :=
  AsSmall.down

private theorem evaluation_down_map {R : CommRingCat.{u}}
    {s t : BoundedFlatAffineSections R} (a : s ⟶ t) :
    (evaluationDown R).map ((boundedFlatAffineSectionEvaluationModelMap R).functor.map a) =
      (boundedFlatAffineOriginalEvaluation R).map a := rfl

private theorem normalizedUnit_app {R S : CommRingCat.{u}} (f : R ⟶ S)
    (θ : boundedFlatPerfectPullback (Spec.map f) ⟶ boundedFlatPerfectPullback (Spec.map f))
    (X : BoundedFlatPerfect (Spec R)) :
    (normalizedWeakTransformation (boundedFlatPerfectPullback_exact (Spec.map f))
      (boundedFlatPerfectPullback_exact (Spec.map f)) θ).app X =
    (boundedFlatPullbackNormalizationIso (Spec.map f)).inv.app X ≫ θ.app X ≫
      (boundedFlatPullbackNormalizationIso (Spec.map f)).hom.app X := rfl

/-- The original evaluation comparison intertwines actual transformations after normalization. -/
theorem boundedFlatAffineSectionModelEvaluation_intertwine
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    (η : (boundedFlatAffineSectionModelMap f).functor ⟶
      (boundedFlatAffineSectionModelMap f).functor)
    (θ : boundedFlatPerfectPullback (Spec.map f) ⟶ boundedFlatPerfectPullback (Spec.map f))
    (h : whiskerRight η (boundedFlatAffineOriginalEvaluation S) ≫
        (boundedFlatAffineSectionCoefficientIso f).hom =
      (boundedFlatAffineSectionCoefficientIso f).hom ≫
        whiskerLeft (boundedFlatAffineOriginalEvaluation R) θ) :
    whiskerRight η (boundedFlatAffineSectionEvaluationModelMap S).functor ≫
        (boundedFlatAffineSectionEvaluationCoefficientIso f).hom =
      (boundedFlatAffineSectionEvaluationCoefficientIso f).hom ≫
        whiskerLeft (boundedFlatAffineSectionEvaluationModelMap R).functor
          (whiskerLeft AsSmall.down (whiskerRight
            (normalizedWeakTransformation (boundedFlatPerfectPullback_exact (Spec.map f))
              (boundedFlatPerfectPullback_exact (Spec.map f)) θ) AsSmall.up)) := by
  apply NatTrans.ext
  funext s
  let : (evaluationDown S).Faithful :=
    (AsSmall.equiv : BoundedFlatPerfect (Spec S) ≌
      (modelOf (boundedFlatPerfectWaldhausen (Spec S))).category).faithful_inverse
  apply (evaluationDown S).map_injective
  have source := evaluation_down_map (R := S) (η.app s)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.map_comp]
  rw [source]
  simp only [coefficientIso_hom_app,
    boundedFlatAffineSectionEvaluationModelMap_functor, Functor.comp_obj,
    AsSmall.down_obj, AsSmall.up_obj_down, evaluationDown, AsSmall.down_map,
    AsSmall.up_map_down, normalizedUnit_app]
  have hs := congrArg (fun τ => τ.app s) h
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hs
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, hs, Category.assoc]

end Quillen.PerfectComplexes
