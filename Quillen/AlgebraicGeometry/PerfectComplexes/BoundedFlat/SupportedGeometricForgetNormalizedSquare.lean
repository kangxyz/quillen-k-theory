/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedTensorForgetRoutes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationModelNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationForgetModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationNaturality

/-! # Geometric support-forgetting squares with the original zero normalizations

The actual supported pullback and ambient pullback meet through the original inclusion.
Their independently selected geometric and support-forgetting zero rebases surround this
square before its common-universe lift. These are the two geometric faces of the full tensor
input cube, rather than a replacement by an evaluation equivalence.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

/-- Normalize the supported geometric pullback and then the original target inclusion. -/
def geometricForgetLeftNormalization :=
  isoWhiskerRight (evaluationRawNormalization p)
      (tensorCoefficientSupportedForget A.obj.hom) ≪≫
    isoWhiskerLeft _ (forgetRawNormalization (X := op A.obj.right) A.obj.hom)

/-- Normalize the original source inclusion and then the actual ambient pullback. -/
def geometricForgetRightNormalization :=
  isoWhiskerRight (forgetRawNormalization (X := op B.obj.right) B.obj.hom)
      (boundedFlatPerfectPullback p.hom.right) ≪≫
    isoWhiskerLeft _ (GlobalSectionChangeIndex.evaluationRawNormalization p.hom.right)

/-- The independent original geometric forgetting face through all four zero comparisons. -/
def geometricForgetNormalizedIso :=
  (geometricForgetLeftNormalization p).symm ≪≫ supportedPullbackForgetIso p ≪≫
    geometricForgetRightNormalization p

/-- The original geometric forgetting face in the actual common-universe Models. -/
def geometricForgetModelIso :
    (evaluationRawMap p ≫ tensorCoefficientSupportedForgetModel A.obj.hom).functor ≅
      (tensorCoefficientSupportedForgetModel B.obj.hom ≫
        GlobalSectionChangeIndex.evaluationRawMap p.hom.right).functor :=
  isoWhiskerRight (isoWhiskerLeft AsSmall.down (geometricForgetNormalizedIso p)) AsSmall.up

/-- The common-universe component retains the independently normalized geometric face. -/
theorem geometricForgetModelIso_hom_app_down
    (K : (modelOf (boundedFlatPerfectSupportedWaldhausen B.obj.hom)).category) :
    ((geometricForgetModelIso p).hom.app K).down =
      (geometricForgetNormalizedIso p).hom.app (AsSmall.down.obj K) := rfl

end Quillen.PerfectComplexes.SupportedTensorEvaluation
