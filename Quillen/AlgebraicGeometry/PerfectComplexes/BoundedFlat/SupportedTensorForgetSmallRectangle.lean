/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedTensorForgetNormalizedRectangle
public import Quillen.Waldhausen.SmallModel.RouteRectangle

/-! # The original tensor/forgetting rectangle in the common universe

The independently normalized supported tensor/forgetting rectangle is lifted through the
original common-universe functors, retaining each chosen-zero normalization on both routes.
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

/-- Original supported tensor evaluation after common-universe transport. -/
def forgetSupportedTensorSmallIso :
    (supportedPairModelMap p).functor ⋙ evaluationSmall (X := op A.obj.right) A.obj.hom ≅
      evaluationSmall (X := op B.obj.right) B.obj.hom ⋙ (tensorSupportedPairModelMap p).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (forgetSupportedTensorNormalizedIso p) AsSmall.up

/-- Original ambient tensor evaluation after the same common-universe transport. -/
def forgetAmbientTensorSmallIso :
    (globalModel.map p.hom.right.op).functor ⋙ GlobalSectionChangeIndex.evaluationSmall
        (op A.obj.right) ≅
      GlobalSectionChangeIndex.evaluationSmall (op B.obj.right) ⋙
        (tensorUnitPullbackModelMap p.hom.right).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (forgetAmbientTensorNormalizedIso p) AsSmall.up

/-- Independent common-universe lifting of the complete raw normalized forgetting square. -/
def tensorForgetModelIso :
    (tensorSupportedPairModelMap p ≫ tensorCoefficientSupportedForgetModel A.obj.hom).functor ≅
      (tensorCoefficientSupportedForgetModel B.obj.hom ≫
        tensorUnitPullbackModelMap p.hom.right).functor :=
  isoWhiskerRight (isoWhiskerLeft AsSmall.down (tensorForgetNormalizedIso p)) AsSmall.up

/-- The actual supported-tensor-first route before evaluation-zero conjugation. -/
def tensorForgetSmallLeftRoute :=
  isoSquareRoute (forgetSupportedTensorSmallIso p)
    (evaluationForgetSmallComparisonIso (X := op A.obj.right) A.obj.hom)

/-- The actual support-forgetting-first route before evaluation-zero conjugation. -/
def tensorForgetSmallRightRoute :=
  isoSquareRoute (evaluationForgetSmallComparisonIso (X := op B.obj.right) B.obj.hom)
    (forgetAmbientTensorSmallIso p)

/-- Common-universe transport preserves the complete independently normalized rectangle. -/
theorem tensorForgetSmallRectangle_hom :
    whiskerLeft (evaluationSmall (X := op B.obj.right) B.obj.hom)
        (tensorForgetModelIso p).hom ≫ (tensorForgetSmallRightRoute p).inv =
      (tensorForgetSmallLeftRoute p).inv ≫
        eqToHom (congrArg (fun F => F ⋙ GlobalSectionChangeIndex.evaluationSmall
          (op A.obj.right)) (forgetReindexInputSquare p)) :=
  smallModelRouteRectangle (forgetSupportedTensorNormalizedIso p)
    (forgetNormalizedIso (X := op A.obj.right) A.obj.hom)
    (forgetNormalizedIso (X := op B.obj.right) B.obj.hom)
    (forgetAmbientTensorNormalizedIso p) (tensorForgetNormalizedIso p)
    (forgetReindexInputSquare p) (tensorForgetNormalizedRectangle_hom p)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
