/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientSmallModel
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedEvaluationModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedPairModel

/-!
# Actual supported tensor evaluation with both selected-zero comparisons

The comparison uses the original supported tensor unitor and the original supported geometric
reindex/evaluation isomorphism. All maps remain between the true supported Models.
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

/-- The original supported tensor unitor after genuine pair pullback. -/
def tensorPairUnitor : tensorSupportedPairFunctor p ≅ boundedFlatPerfectSupportedPullback p :=
  isoWhiskerLeft (boundedFlatPerfectSupportedPullback p)
    (boundedFlatPerfectSupportedTensorUnitIso A.obj.hom)

/-- Retain the actual unitor and geometric evaluation transition in one full supported iso. -/
def tensorEvaluationIso :
    supportedEvaluation (X := op B.obj.right) B.obj.hom ⋙ tensorSupportedPairFunctor p ≅
      (supportedPairModelMap p).functor ⋙
        supportedEvaluation (X := op A.obj.right) A.obj.hom :=
  isoWhiskerLeft _ (tensorPairUnitor p) ≪≫ supportedPairReindexEvaluationIso p

/-- Genuine tensor pullback after the actual supported evaluation Model map. -/
def tensorModelMap :=
  evaluationModel (X := op B.obj.right) B.obj.hom ≫ tensorSupportedPairModelMap p

/-- Original supported reindexing followed by actual target evaluation. -/
def internalModelMap :=
  supportedPairModelMap p ≫ evaluationModel (X := op A.obj.right) A.obj.hom

/-- Original common-universe transport retains the tensor functor's own zero rebase. -/
def tensorMiddleIso :
    ((supportedPairModelMap p).functor ⋙
      supportedEvaluation (X := op A.obj.right) A.obj.hom) ⋙ AsSmall.up ≅
    evaluationSmall (X := op B.obj.right) B.obj.hom ⋙
      (tensorSupportedPairModelMap p).functor :=
  smallModelWhiskerIso (supportedEvaluation (X := op B.obj.right) B.obj.hom)
    ((supportedPairModelMap p).functor ⋙
      supportedEvaluation (X := op A.obj.right) A.obj.hom)
    (tensorSupportedPairFunctor p) _ (tensorEvaluationIso p).symm
    (tensorSupportedPairNormalization p)

/-- Both supported evaluation normalizations are retained in the actual Model comparison. -/
def internalTensorModelIso : (internalModelMap p).functor ≅ (tensorModelMap p).functor :=
  isoWhiskerLeft (supportedPairModelMap p).functor
      (evaluationNormalizationIso (X := op A.obj.right) A.obj.hom).symm ≪≫
    (Functor.associator (supportedPairModelMap p).functor
      (supportedEvaluation (X := op A.obj.right) A.obj.hom) AsSmall.up).symm ≪≫
    tensorMiddleIso p ≪≫
    isoWhiskerRight (evaluationNormalizationIso (X := op B.obj.right) B.obj.hom) _

end Quillen.PerfectComplexes.SupportedTensorEvaluation
