/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorUnitEvaluation

/-!
# Whole original tensor-unit prism on global section inputs

The actual evaluation transition is retained as a path. Its full relative prism identifies
both pastings without replacing a natural isomorphism by a strict functor equality.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- Exactness of genuine tensor pullback on original evaluated global sections. -/
theorem evaluatedTensor_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsExact (globalModel.obj (Opposite.op Y)).waldhausen.cof
      (globalModel.obj (Opposite.op Y)).waldhausen.weq
      (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq
      (globalEvaluation (Opposite.op Y) ⋙ boundedFlatPerfectTensorUnitPullback f) :=
  (globalEvaluation_exact (Opposite.op Y)).comp
    (boundedFlatPerfectTensorUnitPullback_exact f)

/-- Exactness of the original reindexed evaluation, retaining the selected global model. -/
theorem reindexedEvaluation_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsExact (globalModel.obj (Opposite.op Y)).waldhausen.cof
      (globalModel.obj (Opposite.op Y)).waldhausen.weq
      (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq
      ((globalModel.map f.op).functor ⋙ globalEvaluation (Opposite.op X)) :=
  (globalModel.map f.op).exact.comp (globalEvaluation_exact (Opposite.op X))

/-- The actual tensor functor in the existing common-universe presentation. -/
def tensorEvaluationSmallFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (globalEvaluation (Opposite.op Y) ⋙ boundedFlatPerfectTensorUnitPullback f) ⋙
    AsSmall.up

/-- Reindexed evaluation in the same existing common-universe presentation. -/
def reindexedEvaluationSmallFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ((globalModel.map f.op).functor ⋙ globalEvaluation (Opposite.op X)) ⋙ AsSmall.up

/-- The common-universe tensor functor remains exact. -/
theorem tensorEvaluationSmall_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsExact (globalModel.obj (Opposite.op Y)).waldhausen.cof
      (globalModel.obj (Opposite.op Y)).waldhausen.weq
      (boundedFlatPerfectWaldhausen X).smallModel.cof
      (boundedFlatPerfectWaldhausen X).smallModel.weq (tensorEvaluationSmallFunctor f) :=
  (evaluatedTensor_exact f).comp (boundedFlatPerfectWaldhausen X).smallModel_up_exact

/-- Reindexed evaluation is exact in the same presentation. -/
theorem reindexedEvaluationSmall_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsExact (globalModel.obj (Opposite.op Y)).waldhausen.cof
      (globalModel.obj (Opposite.op Y)).waldhausen.weq
      (boundedFlatPerfectWaldhausen X).smallModel.cof
      (boundedFlatPerfectWaldhausen X).smallModel.weq (reindexedEvaluationSmallFunctor f) :=
  (reindexedEvaluation_exact f).comp (boundedFlatPerfectWaldhausen X).smallModel_up_exact

/-- The genuine tensor automorphism in the fixed common universe. -/
def evaluatedTensorSmallUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    tensorEvaluationSmallFunctor f ≅ tensorEvaluationSmallFunctor f :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft (globalEvaluation (Opposite.op Y))
    (boundedFlatPerfectTensorUnitPullbackAutomorphism f r)) AsSmall.up

/-- The same global unit in the fixed common universe. -/
def evaluatedGlobalSmallUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    reindexedEvaluationSmallFunctor f ≅ reindexedEvaluationSmallFunctor f :=
  Functor.isoWhiskerRight (Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (globalModel.map f.op).functor
      (globalUnit (Opposite.op X) r)) (globalEvaluation (Opposite.op X))) AsSmall.up

/-- The original comparison in the fixed common universe. -/
def tensorEvaluationSmallIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorEvaluationSmallFunctor f ≅ reindexedEvaluationSmallFunctor f :=
  Functor.isoWhiskerRight (tensorEvaluationIso f) AsSmall.up

/-- Whiskering retains the complete original tensor-unit square. -/
theorem tensorEvaluationSmall_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    (evaluatedTensorSmallUnit f r).hom ≫ (tensorEvaluationSmallIso f).hom =
      (tensorEvaluationSmallIso f).hom ≫ (evaluatedGlobalSmallUnit f r).hom := by
  have h := congrArg (fun t ↦ Functor.whiskerRight t AsSmall.up)
    (tensorEvaluation_unit f r)
  simpa only [Functor.whiskerRight_comp, evaluatedTensorSmallUnit,
    evaluatedGlobalSmallUnit, tensorEvaluationSmallIso, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, tensorEvaluationSmallFunctor,
    reindexedEvaluationSmallFunctor] using h

/-- The actual tensor track after the fixed common-universe presentation. -/
def evaluatedTensorTrack {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (tensorEvaluationSmall_exact f)
    (tensorEvaluationSmall_exact f) (evaluatedTensorSmallUnit f r)

/-- The full realization of the original comparison. -/
def tensorEvaluationTrack {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (tensorEvaluationSmall_exact f)
    (reindexedEvaluationSmall_exact f) (tensorEvaluationSmallIso f)

/-- The original global unit on reindexed evaluation, with its complete track. -/
def reindexedGlobalUnitTrack {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (reindexedEvaluationSmall_exact f)
    (reindexedEvaluationSmall_exact f) (evaluatedGlobalSmallUnit f r)

/-- Actual tensor and original global unit have the complete endpoint-relative prism. -/
def tensorEvaluationPasting {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    ((evaluatedTensorTrack f r).trans (tensorEvaluationTrack f)).RelHomotopy
      ((tensorEvaluationTrack f).trans (reindexedGlobalUnitTrack f r)) :=
  exactOriginalPrespectrumPastingHomotopy _ _
    (tensorEvaluationSmall_exact f) (tensorEvaluationSmall_exact f)
    (reindexedEvaluationSmall_exact f) (reindexedEvaluationSmall_exact f)
    (evaluatedTensorSmallUnit f r).hom
    (tensorEvaluationSmallIso f).hom (tensorEvaluationSmallIso f).hom
    (evaluatedGlobalSmallUnit f r).hom
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
    (tensorEvaluationSmall_unit f r)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
