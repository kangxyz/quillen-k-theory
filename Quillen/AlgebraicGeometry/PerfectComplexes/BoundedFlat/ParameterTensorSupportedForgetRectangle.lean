/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedTensorForgetModelRectangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedRow
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorModelComparison

/-! # The actual parameter tensor/forgetting evaluation rectangle

The supported Laurent coefficient pair specializes the complete normalized Model rectangle.
Its ambient comparison is identified with the original parameter tensor/evaluation comparison,
so the result retains the actual parameter maps rather than a replacement ambient route.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.ParameterTensorSupportedRow
open GlobalSectionChangeIndex SupportedTensorEvaluation
attribute [local irreducible] globalModel globalEvaluation
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (X : Scheme.{u}ᵒᵖ)

/-- The ambient edge is precisely the original actual parameter tensor Model comparison. -/
theorem forgetAmbientTensorModelIso_parameter :
    forgetAmbientTensorModelIso (coefficientPair f X) =
      ParameterTensorEvaluationRow.internalTensorModelIso Q X := by
  simp only [forgetAmbientTensorModelIso, isoSquareConjugate, forgetAmbientTensorSmallIso,
    forgetAmbientTensorNormalizedIso, ParameterTensorEvaluationRow.internalTensorModelIso,
    ParameterTensorEvaluationRow.tensorMiddleIso, smallModelWhiskerIso, Iso.trans_assoc]
  rfl

/-- Forgetting genuine supported parameter tensor inputs preserves the complete Model rectangle. -/
theorem modelEvaluationForgetRectangle_hom :
    whiskerLeft (SupportedTensorEvaluation.evaluationModel
        (X := op (pair f X).obj.right) (pair f X).obj.hom).functor
        (tensorForgetModelIso (coefficientPair f X)).hom ≫
        (isoSquareRoute (evaluationForgetModelComparisonIso
          (X := op (pair f X).obj.right) (pair f X).obj.hom)
          (ParameterTensorEvaluationRow.internalTensorModelIso Q X)).inv =
      (tensorForgetModelLeftRoute (coefficientPair f X)).inv ≫
        eqToHom (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel
            (op (pair f (laurent.op.obj X)).obj.right)).functor)
          (forgetReindexInputSquare (coefficientPair f X))) := by
  rw [← forgetAmbientTensorModelIso_parameter f X]
  exact tensorForgetModelRectangle_hom (coefficientPair f X)

/-- Equality of both complete original parameter Model routes, including their source transport. -/
theorem modelEvaluationForgetRectangle :
    isoWhiskerLeft (SupportedTensorEvaluation.evaluationModel
        (X := op (pair f X).obj.right) (pair f X).obj.hom).functor
        (tensorForgetModelIso (coefficientPair f X)) ≪≫
        (isoSquareRoute (evaluationForgetModelComparisonIso
          (X := op (pair f X).obj.right) (pair f X).obj.hom)
          (ParameterTensorEvaluationRow.internalTensorModelIso Q X)).symm =
      (tensorForgetModelLeftRoute (coefficientPair f X)).symm ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel
            (op (pair f (laurent.op.obj X)).obj.right)).functor)
          (forgetReindexInputSquare (coefficientPair f X))) :=
  Iso.ext (modelEvaluationForgetRectangle_hom f X)

end Quillen.PerfectComplexes.ParameterTensorSupportedRow
