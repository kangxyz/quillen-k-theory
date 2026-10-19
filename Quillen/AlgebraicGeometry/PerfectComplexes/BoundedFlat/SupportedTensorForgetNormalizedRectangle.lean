/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedTensorForgetRawRectangle
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteTargetNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitIteratedPrism

/-! # The tensor/forgetting rectangle through all original geometric zero rebases

The independently defined supported tensor/forgetting square is surrounded by the four actual
chosen-zero normalization isomorphisms. Its two complete evaluation routes retain these paths.
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

/-- Normalize the supported tensor leg and then the original target support inclusion. -/
def tensorForgetLeftNormalization :=
  isoWhiskerRight (tensorSupportedPairNormalization p)
      (tensorCoefficientSupportedForget A.obj.hom) ≪≫
    isoWhiskerLeft (tensorSupportedPairNormalizedFunctor p)
      (forgetRawNormalization (X := op A.obj.right) A.obj.hom)

/-- Normalize the original source support inclusion and then the ambient tensor leg. -/
def tensorForgetRightNormalization :=
  isoWhiskerRight (forgetRawNormalization (X := op B.obj.right) B.obj.hom)
      (boundedFlatPerfectTensorUnitPullback p.hom.right) ≪≫
    isoWhiskerLeft _ (tensorUnitPullbackNormalization p.hom.right)

/-- The actual raw forgetting square surrounded by all four original zero rebases. -/
def tensorForgetNormalizedIso :=
  (tensorForgetLeftNormalization p).symm ≪≫ tensorSupportedPairForgetIso p ≪≫
    tensorForgetRightNormalization p

/-- The independently normalized supported tensor/evaluation edge. -/
def forgetSupportedTensorNormalizedIso :=
  (tensorEvaluationIso p).symm ≪≫
    isoWhiskerLeft (supportedEvaluation (X := op B.obj.right) B.obj.hom)
      (tensorSupportedPairNormalization p)

/-- The independently normalized ambient tensor/evaluation edge. -/
def forgetAmbientTensorNormalizedIso :=
  (GlobalSectionChangeIndex.tensorEvaluationIso p.hom.right).symm ≪≫
    isoWhiskerLeft (globalEvaluation (op B.obj.right))
      (tensorUnitPullbackNormalization p.hom.right)

/-- The actual inclusion/evaluation edge with its own geometric zero rebase. -/
def forgetNormalizedIso {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}}
    (j : U ⟶ X.unop) [IsOpenImmersion j] :=
  evaluationForgetIso j ≪≫ isoWhiskerLeft (supportedEvaluation j) (forgetRawNormalization j)

/-- The complete supported-tensor-first normalized route. -/
def tensorForgetNormalizedLeftRoute :=
  isoSquareRoute (forgetSupportedTensorNormalizedIso p)
    (forgetNormalizedIso (X := op A.obj.right) A.obj.hom)

/-- The complete support-forgetting-first normalized route. -/
def tensorForgetNormalizedRightRoute :=
  isoSquareRoute (forgetNormalizedIso (X := op B.obj.right) B.obj.hom)
    (forgetAmbientTensorNormalizedIso p)

/-- All four original geometric zero comparisons preserve the whole two-route rectangle. -/
theorem tensorForgetNormalizedRectangle_hom :
    whiskerLeft (supportedEvaluation (X := op B.obj.right) B.obj.hom)
        (tensorForgetNormalizedIso p).hom ≫ (tensorForgetNormalizedRightRoute p).inv =
      (tensorForgetNormalizedLeftRoute p).inv ≫
        eqToHom (congrArg (fun F => F ⋙ globalEvaluation (op A.obj.right))
          (forgetReindexInputSquare p)) := by
  unfold tensorForgetNormalizedLeftRoute tensorForgetNormalizedRightRoute
    forgetSupportedTensorNormalizedIso forgetAmbientTensorNormalizedIso forgetNormalizedIso
  rw [isoSquareRoute_targetNormalization, isoSquareRoute_targetNormalization]
  exact isoSquareTargetNormalization_rectangle
    (isoSquareRoute (tensorEvaluationIso p).symm
      (evaluationForgetIso (X := op A.obj.right) A.obj.hom))
    (isoSquareRoute (evaluationForgetIso (X := op B.obj.right) B.obj.hom)
      (GlobalSectionChangeIndex.tensorEvaluationIso p.hom.right).symm)
    (tensorSupportedPairForgetIso p) (forgetReindexInputSquare p)
    (tensorForgetLeftNormalization p) (tensorForgetRightNormalization p)
    (tensorForgetRawRectangle_hom p)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
