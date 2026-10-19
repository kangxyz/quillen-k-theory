/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedForgetRectangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportMaps

/-! # Tensor and support-forgetting rectangles on the three original auxiliary objects

The union-supported, auxiliary-supported, and inverse-open-supported parameter Models each
retain the original tensor comparison and its complete evaluated support-forgetting rectangle.
Every selected-zero rebase and both evaluation normalizations are inherited from the actual
parameter comparison; none of the three supported objects is replaced by an ambient fiber.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open ParameterTensorSupportedRow SupportedTensorEvaluation
attribute [local irreducible] globalModel globalEvaluation
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original union-supported object has the complete tensor/forgetting Model rectangle. -/
theorem unionTensorForgetRectangle (X : Scheme.{u}ᵒᵖ) :
    let j := (unionOpen f T).ι
    isoWhiskerLeft (SupportedTensorEvaluation.evaluationModel
        (X := op (pair j X).obj.right) (pair j X).obj.hom).functor
        (tensorForgetModelIso (coefficientPair j X)) ≪≫
        (isoSquareRoute (evaluationForgetModelComparisonIso
          (X := op (pair j X).obj.right) (pair j X).obj.hom)
          (ParameterTensorEvaluationRow.internalTensorModelIso Q X)).symm =
      (tensorForgetModelLeftRoute (coefficientPair j X)).symm ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel
            (op (pair j (laurent.op.obj X)).obj.right)).functor)
          (forgetReindexInputSquare (coefficientPair j X))) :=
  modelEvaluationForgetRectangle (unionOpen f T).ι X

/-- The original auxiliary-supported object has the complete tensor/forgetting Model rectangle. -/
theorem auxiliaryTensorForgetRectangle (X : Scheme.{u}ᵒᵖ) :
    let j := T.ι
    isoWhiskerLeft (SupportedTensorEvaluation.evaluationModel
        (X := op (pair j X).obj.right) (pair j X).obj.hom).functor
        (tensorForgetModelIso (coefficientPair j X)) ≪≫
        (isoSquareRoute (evaluationForgetModelComparisonIso
          (X := op (pair j X).obj.right) (pair j X).obj.hom)
          (ParameterTensorEvaluationRow.internalTensorModelIso Q X)).symm =
      (tensorForgetModelLeftRoute (coefficientPair j X)).symm ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel
            (op (pair j (laurent.op.obj X)).obj.right)).functor)
          (forgetReindexInputSquare (coefficientPair j X))) :=
  modelEvaluationForgetRectangle T.ι X

omit [IsOpenImmersion f] in
/-- The original inverse-open-supported object has the complete tensor/forgetting rectangle. -/
theorem inverseOpenTensorForgetRectangle (X : Scheme.{u}ᵒᵖ) :
    let j := (inverseOpen f T).ι
    isoWhiskerLeft (SupportedTensorEvaluation.evaluationModel
        (X := op (pair j X).obj.right) (pair j X).obj.hom).functor
        (tensorForgetModelIso (coefficientPair j X)) ≪≫
        (isoSquareRoute (evaluationForgetModelComparisonIso
          (X := op (pair j X).obj.right) (pair j X).obj.hom)
          (ParameterTensorEvaluationRow.internalTensorModelIso P X)).symm =
      (tensorForgetModelLeftRoute (coefficientPair j X)).symm ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel
            (op (pair j (laurent.op.obj X)).obj.right)).functor)
          (forgetReindexInputSquare (coefficientPair j X))) :=
  modelEvaluationForgetRectangle (inverseOpen f T).ι X

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
