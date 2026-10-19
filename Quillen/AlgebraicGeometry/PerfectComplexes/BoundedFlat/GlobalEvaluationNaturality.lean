/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumIntertwiningHomotopy

/-! # Original geometric evaluation comparison with both chosen-zero normalizations -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The original raw geometric model map with its actual zero normalization. -/
def evaluationRawMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modelOf (boundedFlatPerfectWaldhausen Y) ⟶ modelOf (boundedFlatPerfectWaldhausen X) :=
  modelMap _ _ (boundedFlatPerfectPullback_exact f).rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _)

/-- The actual raw normalization isomorphism before common-universe lifting. -/
def evaluationRawNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Quillen.rebaseFunctorIso (boundedFlatPerfectPullback f)
    (boundedFlatPerfectWaldhausen Y).zero (boundedFlatPerfectWaldhausen X).zero
    (((boundedFlatPerfectPullback_exact f).zero (boundedFlatPerfectWaldhausen Y).isZero).iso
      (boundedFlatPerfectWaldhausen X).isZero)

/-- Lift the actual evaluation transition and original raw zero normalization. -/
def evaluationMiddleIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((globalModel.map f.op).functor ⋙ globalEvaluation (Opposite.op X)) ⋙ AsSmall.up ≅
      evaluationSmall (Opposite.op Y) ⋙ (evaluationRawMap f).functor :=
  smallModelWhiskerIso (globalEvaluation (Opposite.op Y))
    ((globalModel.map f.op).functor ⋙ globalEvaluation (Opposite.op X))
    (boundedFlatPerfectPullback f) _ (evaluationPullbackIso f).symm
    (evaluationRawNormalization f)

/-- Preserve the complete original geometric comparison rather than declaring a strict square. -/
def evaluationComparisonIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (globalModel.map f.op ≫ evaluationModel (Opposite.op X)).functor ≅
      (evaluationModel (Opposite.op Y) ≫ evaluationRawMap f).functor :=
  isoWhiskerLeft (globalModel.map f.op).functor
      (evaluationNormalizationIso (Opposite.op X)).symm ≪≫
    (Functor.associator (globalModel.map f.op).functor
      (globalEvaluation (Opposite.op X)) AsSmall.up).symm ≪≫
    evaluationMiddleIso f ≪≫
    isoWhiskerRight (evaluationNormalizationIso (Opposite.op Y)) _

/-- The original comparison keeps every spectrum level and its independent structure coordinate. -/
def evaluationComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy
      (prespectrumMap (globalModel.map f.op) ≫ prespectrumMap (evaluationModel (Opposite.op X)))
      (prespectrumMap (evaluationModel (Opposite.op Y)) ≫ prespectrumMap (evaluationRawMap f)) :=
  (prespectrumTransformationHomotopy
    (V := globalModel.obj (Opposite.op Y))
    (W := modelOf (boundedFlatPerfectWaldhausen X))
    (F := globalModel.map f.op ≫ evaluationModel (Opposite.op X))
    (G := evaluationModel (Opposite.op Y) ≫ evaluationRawMap f)
    (evaluationComparisonIso f).hom
    (fun A ↦ (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _
      (inferInstanceAs (IsIso ((evaluationComparisonIso f).app A).hom)))).cast
      (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_comp _ _)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
