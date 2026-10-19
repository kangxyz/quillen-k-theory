/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedNormalizedInputSquare

/-! # Exact original supported Model evaluation edges

The actual tensor and geometric Model comparisons are identified with their original small
supported coefficient comparisons conjugated by the specified evaluation zero isomorphisms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen
universe u v w
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

attribute [local irreducible] evaluationNormalizationIso
  tensorSupportedPairNormalization tensorPairUnitor supportedPairReindexEvaluationIso

private theorem tensorWhisker {C : Type*} [Category* C]
    {D E : Type v} [Category.{w} D] [Category.{w} E]
    (A : C ⥤ D) (B : C ⥤ E) (P T N : D ⥤ E)
    (v : T ≅ P) (c : A ⋙ P ≅ B) (n : T ≅ N) :
    smallModelWhiskerIso A B T N ((isoWhiskerLeft A v) ≪≫ c).symm n =
      isoWhiskerRight (c.symm ≪≫ isoWhiskerLeft A (v.symm ≪≫ n))
        AsSmall.up.{w, v, 0} := by
  simp only [smallModelWhiskerIso, Iso.trans_symm, isoWhiskerLeft_symm,
    isoWhiskerLeft_trans, Iso.trans_assoc]

private theorem tensorMiddleIso_coefficient :
    tensorMiddleIso p =
      isoWhiskerRight
        (supportedNormalizedCoefficientIso p (supportedTensorCoefficientNormalization p))
        AsSmall.up.{u, u + 1, 0} := by
  have h := tensorWhisker
    (supportedEvaluation (X := op B.obj.right) B.obj.hom)
    ((supportedPairModelMap p).functor ⋙
      supportedEvaluation (X := op A.obj.right) A.obj.hom)
    (boundedFlatPerfectSupportedPullback p) (tensorSupportedPairFunctor p) _
    (tensorPairUnitor p) (supportedPairReindexEvaluationIso p)
    (tensorSupportedPairNormalization p)
  simpa only [tensorMiddleIso, tensorEvaluationIso, supportedNormalizedCoefficientIso,
    supportedTensorCoefficientNormalization, evaluationSmall] using h

/-- The actual supported tensor Model comparison retains the full original coefficient edge. -/
theorem internalTensorModelIso_smallCoefficient :
    internalTensorModelIso p =
      isoSquareConjugate
        (supportedSmallCoefficientIso p (supportedTensorCoefficientNormalization p))
        (evaluationNormalizationIso (X := op B.obj.right) B.obj.hom)
        (evaluationNormalizationIso (X := op A.obj.right) A.obj.hom) := by
  simp only [internalTensorModelIso, isoSquareConjugate, supportedSmallCoefficientIso,
    tensorMiddleIso_coefficient, Iso.trans_assoc]
  rfl

/-- The actual supported geometric Model edge retains its original small coefficient comparison. -/
theorem evaluationComparisonIso_smallCoefficient :
    evaluationComparisonIso p =
      isoSquareConjugate
        (supportedSmallCoefficientIso p (evaluationRawNormalization p))
        (evaluationNormalizationIso (X := op B.obj.right) B.obj.hom)
        (evaluationNormalizationIso (X := op A.obj.right) A.obj.hom) := rfl

end Quillen.PerfectComplexes.SupportedTensorEvaluation
