/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedTensorForgetSmallRectangle
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteRectangle

/-! # The complete original tensor/forgetting Model rectangle

The raw supported tensor/forgetting comparison is normalized independently and lifted through
the genuine common-universe functors. The complete Model rectangle retains both endpoint
evaluation normalizations and the intermediate normalization on each actual route.
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

/-- The original supported tensor Model edge is the genuine small edge at its two corners. -/
theorem internalTensorModelIso_forgetSmall :
    internalTensorModelIso p = isoSquareConjugate (forgetSupportedTensorSmallIso p)
      (evaluationNormalizationIso (X := op B.obj.right) B.obj.hom)
      (evaluationNormalizationIso (X := op A.obj.right) A.obj.hom) := by
  simp only [internalTensorModelIso, isoSquareConjugate, forgetSupportedTensorSmallIso,
    tensorMiddleIso, smallModelWhiskerIso, forgetSupportedTensorNormalizedIso, Iso.trans_assoc]

/-- The ambient tensor Model edge retains the two original ambient evaluation normalizations. -/
def forgetAmbientTensorModelIso :=
  isoSquareConjugate (forgetAmbientTensorSmallIso p)
    (GlobalSectionChangeIndex.evaluationNormalizationIso (op B.obj.right))
    (GlobalSectionChangeIndex.evaluationNormalizationIso (op A.obj.right))

/-- The original supported-tensor-first route with every actual evaluation normalization. -/
def tensorForgetModelLeftRoute :=
  isoSquareRoute (internalTensorModelIso p)
    (evaluationForgetModelComparisonIso (X := op A.obj.right) A.obj.hom)

/-- The original support-forgetting-first route with every actual evaluation normalization. -/
def tensorForgetModelRightRoute :=
  isoSquareRoute (evaluationForgetModelComparisonIso (X := op B.obj.right) B.obj.hom)
    (forgetAmbientTensorModelIso p)

/-- The whole Model-level rectangle retains the original tensor and all support-forgetting paths. -/
theorem tensorForgetModelRectangle_hom :
    whiskerLeft (evaluationModel (X := op B.obj.right) B.obj.hom).functor
        (tensorForgetModelIso p).hom ≫ (tensorForgetModelRightRoute p).inv =
      (tensorForgetModelLeftRoute p).inv ≫
        eqToHom (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel (op A.obj.right)).functor)
          (forgetReindexInputSquare p)) := by
  unfold tensorForgetModelLeftRoute tensorForgetModelRightRoute
  rw [internalTensorModelIso_forgetSmall]
  unfold evaluationForgetModelComparisonIso forgetAmbientTensorModelIso
  rw [isoSquareRoute_conjugate, isoSquareRoute_conjugate]
  exact isoSquareConjugate_rectangle (tensorForgetSmallLeftRoute p)
    (tensorForgetSmallRightRoute p) (tensorForgetModelIso p) (forgetReindexInputSquare p)
    (evaluationNormalizationIso (X := op B.obj.right) B.obj.hom)
    (GlobalSectionChangeIndex.evaluationNormalizationIso (op A.obj.right))
    (tensorForgetSmallRectangle_hom p)

/-- Equality of the full specified Model isomorphism routes, including their source transport. -/
theorem tensorForgetModelRectangle :
    isoWhiskerLeft (evaluationModel (X := op B.obj.right) B.obj.hom).functor
        (tensorForgetModelIso p) ≪≫ (tensorForgetModelRightRoute p).symm =
      (tensorForgetModelLeftRoute p).symm ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel (op A.obj.right)).functor)
          (forgetReindexInputSquare p)) := by
  apply Iso.ext
  exact tensorForgetModelRectangle_hom p

end Quillen.PerfectComplexes.SupportedTensorEvaluation
