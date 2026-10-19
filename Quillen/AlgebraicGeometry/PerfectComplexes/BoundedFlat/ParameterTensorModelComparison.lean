/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorEvaluationRow
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitIteratedPrism

/-!
# The actual tensor and internal coefficient Model comparison

The original tensor unitor and evaluation transition are transported through both selected-zero
normalizations. The result compares actual Model functors and is not a strict evaluation square.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

/-- The normalized genuine tensor map after actual parameter evaluation. -/
def tensorModelMap (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  evaluationModel (op (scheme Q X)) ≫ tensorUnitPullbackModelMap (coefficientMap Q X)

/-- The original coefficient map followed by actual target evaluation. -/
def internalModelMap (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  globalModel.map (coefficientMap Q X).op ≫
    evaluationModel (op (scheme Q (laurent.op.obj X)))

/-- Common-universe transport of the genuine tensor comparison and its original raw rebase. -/
def tensorMiddleIso (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ((globalModel.map (coefficientMap Q X).op).functor ⋙
      globalEvaluation (op (scheme Q (laurent.op.obj X)))) ⋙ AsSmall.up ≅
    evaluationSmall (op (scheme Q X)) ⋙
      (tensorUnitPullbackModelMap (coefficientMap Q X)).functor :=
  smallModelWhiskerIso (globalEvaluation (op (scheme Q X)))
    ((globalModel.map (coefficientMap Q X).op).functor ⋙
      globalEvaluation (op (scheme Q (laurent.op.obj X))))
    (boundedFlatPerfectTensorUnitPullback (coefficientMap Q X)) _
    (tensorEvaluationIso (coefficientMap Q X)).symm
    (tensorUnitPullbackNormalization (coefficientMap Q X))

/-- The complete functor isomorphism retains both actual evaluation zero normalizations. -/
def internalTensorModelIso (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (internalModelMap Q X).functor ≅ (tensorModelMap Q X).functor :=
  isoWhiskerLeft (globalModel.map (coefficientMap Q X).op).functor
      (evaluationNormalizationIso (op (scheme Q (laurent.op.obj X)))).symm ≪≫
    (Functor.associator (globalModel.map (coefficientMap Q X).op).functor
      (globalEvaluation (op (scheme Q (laurent.op.obj X)))) AsSmall.up).symm ≪≫
    tensorMiddleIso Q X ≪≫
    isoWhiskerRight (evaluationNormalizationIso (op (scheme Q X))) _

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
