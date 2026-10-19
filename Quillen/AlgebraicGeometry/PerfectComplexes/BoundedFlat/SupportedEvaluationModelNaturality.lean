/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedEvaluationModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedPairModel
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation

/-! # Actual geometric supported evaluation with its original zero normalizations

These edges use the original supported pair transition, the genuine supported pullback,
and precisely their selected-zero normalizations. No new compatibility is assumed.
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
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

/-- The raw supported geometric map with its actual chosen-zero rebase. -/
def evaluationRawMap :
    modelOf (boundedFlatPerfectSupportedWaldhausen B.obj.hom) ⟶
      modelOf (boundedFlatPerfectSupportedWaldhausen A.obj.hom) :=
  modelMap _ _ (boundedFlatPerfectSupportedPullback_exact p).rebase
    (Quillen.rebaseFunctor_obj_base _ _ _ _)

/-- The original supported geometric zero normalization before universe transport. -/
def evaluationRawNormalization :=
  Quillen.rebaseFunctorIso (boundedFlatPerfectSupportedPullback p)
    (boundedFlatPerfectSupportedWaldhausen B.obj.hom).zero
    (boundedFlatPerfectSupportedWaldhausen A.obj.hom).zero
    (((boundedFlatPerfectSupportedPullback_exact p).zero
      (boundedFlatPerfectSupportedWaldhausen B.obj.hom).isZero).iso
      (boundedFlatPerfectSupportedWaldhausen A.obj.hom).isZero)

/-- The original geometric edge in the actual common-universe supported categories. -/
def evaluationSmallComparisonIso :
    (supportedPairModelMap p).functor ⋙
        evaluationSmall (X := op A.obj.right) A.obj.hom ≅
      evaluationSmall (X := op B.obj.right) B.obj.hom ⋙ (evaluationRawMap p).functor :=
  (Functor.associator _ _ _).symm ≪≫
    smallModelWhiskerIso (supportedEvaluation (X := op B.obj.right) B.obj.hom)
      ((supportedPairModelMap p).functor ⋙
        supportedEvaluation (X := op A.obj.right) A.obj.hom)
      (boundedFlatPerfectSupportedPullback p) _ (supportedPairReindexEvaluationIso p).symm
      (evaluationRawNormalization p)

/-- Both actual supported evaluation zero normalizations remain in the full Model edge. -/
def evaluationComparisonIso :
    (supportedPairModelMap p ≫ evaluationModel (X := op A.obj.right) A.obj.hom).functor ≅
      (evaluationModel (X := op B.obj.right) B.obj.hom ≫ evaluationRawMap p).functor :=
  isoSquareConjugate (evaluationSmallComparisonIso p)
    (evaluationNormalizationIso (X := op B.obj.right) B.obj.hom)
    (evaluationNormalizationIso (X := op A.obj.right) A.obj.hom)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
