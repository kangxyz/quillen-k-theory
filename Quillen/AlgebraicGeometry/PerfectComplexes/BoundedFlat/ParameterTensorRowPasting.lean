/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorModelUnit
public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationPasting

/-! # The actual ambient tensor/evaluation first-row prism

Both sides use the original forward unit. The comparison retains the tensor unitor, evaluation
pseudonaturality and selected-zero normalizations as its actual endpoint path. The genuine row
coordinate is retained by the row spectrum target rather than replaced by K of the row category.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

/-- Evaluate the original internal forward unit on the actual coefficient Model map. -/
def internalModelUnit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (internalModelMap Q X).functor ⟶ (internalModelMap Q X).functor :=
  whiskerRight
    (onFunctor (globalModel.map (coefficientMap Q X).op).functor
      (globalUnit (op (scheme Q (laurent.op.obj X)))
        (ParameterLaurentUnit.projectedLaurentScalar Q X))).hom
    (evaluationModel (op (scheme Q (laurent.op.obj X)))).functor

/-- The original normalized genuine tensor multiplication after source evaluation. -/
def tensorModelUnit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (tensorModelMap Q X).functor ⟶ (tensorModelMap Q X).functor :=
  whiskerLeft (evaluationModel (op (scheme Q X))).functor
    (tensorUnitPullbackModelTransformation (coefficientMap Q X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X))

/-- Exact evaluation preserves the original internal unit's weak equivalence. -/
theorem internalModelUnit_weak (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (A : (ParameterModels.ambient Q).obj X) :
    (modelOf (boundedFlatPerfectWaldhausen (scheme Q (laurent.op.obj X)))).waldhausen.weq
      ((internalModelUnit Q X).app A) :=
  (evaluationModel (op (scheme Q (laurent.op.obj X)))).exact.weak _
    ((globalModel.obj (op (scheme Q (laurent.op.obj X)))).waldhausen.weq_iso _ inferInstance)

/-- Actual source evaluation retains the true tensor crossing's weak equivalence. -/
theorem tensorModelUnit_weak (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (A : (ParameterModels.ambient Q).obj X) :
    (modelOf (boundedFlatPerfectWaldhausen (scheme Q (laurent.op.obj X)))).waldhausen.weq
      ((tensorModelUnit Q X).app A) :=
  tensorUnitPullbackModelTransformation_weak (coefficientMap Q X)
    (ParameterLaurentUnit.projectedLaurentScalar Q X)
    ((evaluationModel (op (scheme Q X))).functor.obj A)

/-- The entire endpoint-relative first-row prism, preserving both original zero normalizations. -/
def tensorRowPasting (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  rowTransformationPasting
    (F := internalModelMap Q X) (G := internalModelMap Q X)
    (G' := tensorModelMap Q X) (H := tensorModelMap Q X)
    (internalModelUnit Q X) (internalTensorModelIso Q X).hom
    (internalTensorModelIso Q X).hom (tensorModelUnit Q X)
    (internalModelUnit_weak Q X)
    (fun _ => (modelOf (boundedFlatPerfectWaldhausen
      (scheme Q (laurent.op.obj X)))).waldhausen.weq_iso _ inferInstance)
    (fun _ => (modelOf (boundedFlatPerfectWaldhausen
      (scheme Q (laurent.op.obj X)))).waldhausen.weq_iso _ inferInstance)
    (tensorModelUnit_weak Q X) (internalTensorModelIso_unit Q X)

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
