/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorRawInput
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedInput
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitRawModelInputSquare

/-! # The actual two evaluated Model routes of the parameter tensor input square

The left route uses the specified tensor/evaluation comparison then the original geometric
evaluation comparison. The right route uses these in the opposite order. Both retain their
original chosen-zero normalizations and categorical associators.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex
variable (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y)

/-- Evaluation of the independently constructed based raw tensor input square. -/
def rawEvaluatedInputIso :=
  isoWhiskerLeft (evaluationModel (op (scheme Q X))).functor
    (tensorUnitRawModelInputIso (coefficientMap Q X) (coefficientMap Q Y)
      (inputSchemeMap Q (laurent.op.map g)) (inputSchemeMap Q g) (coefficientMap_input Q g))

/-- First use the tensor comparison, then the genuine geometric evaluation comparison. -/
def modelEvaluationInputLeft :=
  isoWhiskerRight (internalTensorModelIso Q X).symm
      (evaluationRawMap (inputSchemeMap Q (laurent.op.map g))).functor ≪≫
    Functor.associator (globalModel.map (coefficientMap Q X).op).functor
      (evaluationModel (op (scheme Q (laurent.op.obj X)))).functor
      (evaluationRawMap (inputSchemeMap Q (laurent.op.map g))).functor ≪≫
    isoWhiskerLeft (globalModel.map (coefficientMap Q X).op).functor
      (evaluationComparisonIso (inputSchemeMap Q (laurent.op.map g))).symm ≪≫
    (Functor.associator (globalModel.map (coefficientMap Q X).op).functor
      (globalModel.map (inputSchemeMap Q (laurent.op.map g)).op).functor
      (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor).symm

/-- First use the geometric evaluation comparison, then the specified tensor comparison. -/
def modelEvaluationInputRight :=
  isoWhiskerRight (evaluationComparisonIso (inputSchemeMap Q g)).symm
      (tensorUnitPullbackModelMap (coefficientMap Q Y)).functor ≪≫
    Functor.associator (globalModel.map (inputSchemeMap Q g).op).functor
      (evaluationModel (op (scheme Q Y))).functor
      (tensorUnitPullbackModelMap (coefficientMap Q Y)).functor ≪≫
    isoWhiskerLeft (globalModel.map (inputSchemeMap Q g).op).functor
      (internalTensorModelIso Q Y).symm ≪≫
    (Functor.associator (globalModel.map (inputSchemeMap Q g).op).functor
      (globalModel.map (coefficientMap Q Y).op).functor
      (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor).symm

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
