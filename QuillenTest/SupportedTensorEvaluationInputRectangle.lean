/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryTensorInputRectangle

/-! # Original supported parameter transport determines the evaluated tensor comparison

The parameter arrow is arbitrary. This client recovers the entire independently defined raw
comparison from its two evaluation routes and the original parameter coefficient square.
-/
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.SupportedTensorEvaluation
universe u
namespace QuillenTest.SupportedTensorEvaluationInputRectangle

private theorem recoverIso {C : Type*} [Category* C] {W X Y Z : C}
    (r : W ≅ X) (s : X ≅ Z) (l : W ≅ Y) (t : Y ≅ Z)
    (h : l ≪≫ t = r ≪≫ s) : r = (l ≪≫ t) ≪≫ s.symm := by
  rw [h]
  simp

/-- Arbitrary original scheme input determines the full supported raw tensor comparison. -/
theorem recover_parameter_input {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    rawEvaluatedInputIso
        (ParameterTensorSupportedRow.coefficientPair f X)
        (ParameterTensorSupportedRow.coefficientPair f Y)
        (ParameterTensorSupportedRow.inputPair f (laurent.op.map g))
        (ParameterTensorSupportedRow.inputPair f g)
        (ParameterTensorSupportedRow.coefficientPair_input f g) =
      (modelEvaluationInputLeft (ParameterTensorSupportedRow.coefficientPair f X)
          (ParameterTensorSupportedRow.inputPair f (laurent.op.map g)) ≪≫
        isoWhiskerRight
          (ParameterTensorEvaluationRow.coefficientFunctorSquare (ParameterModels.supported f) g)
          (SupportedTensorEvaluation.evaluationModel
            (X := op (ParameterTensorSupportedRow.pair f (laurent.op.obj Y)).obj.right)
            (ParameterTensorSupportedRow.pair f (laurent.op.obj Y)).obj.hom).functor) ≪≫
        (modelEvaluationInputRight (ParameterTensorSupportedRow.coefficientPair f Y)
          (ParameterTensorSupportedRow.inputPair f g)).symm :=
  recoverIso _ _ _ _ (ParameterTensorSupportedRow.modelEvaluationInputSquare f g)

end QuillenTest.SupportedTensorEvaluationInputRectangle
