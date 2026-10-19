/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorInitialCell
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# The genuine tensor cell returned to the original parameter Model

Both the actual tensor multiplication and its evaluation/unitor endpoint path pass
through the exact categorical inverse. The two-cylinder first-row realization is
retained, and its complete endpoint-relative prism now lies in the original Model's
row target. This is the common target needed before the original Bass inclusion.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

/-- The exact inverse preserves weakness of the original tensor multiplication. -/
theorem returnedTensorUnit_weak (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (A : (ParameterModels.ambient Q).obj X) :
    (globalModel.obj (op (scheme Q (laurent.op.obj X)))).waldhausen.weq
      ((returnedTensorUnit Q X).app A) :=
  (evaluationInverseModel (op (scheme Q (laurent.op.obj X)))).exact.weak _
    (tensorModelUnit_weak Q X A)

/-- The independently realized tensor cell after the actual exact inverse. -/
def returnedTensorCell (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  rowTransformationSpectrumHomotopy (F := returnedTensorModel Q X)
    (G := returnedTensorModel Q X) (returnedTensorUnit Q X) (returnedTensorUnit_weak Q X)

/-- The original unit of evaluation and genuine tensor unitor give this actual moving endpoint.
-/
def returnedMovement (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  rowTransformationSpectrumHomotopy
    (F := globalModel.map (coefficientMap Q X).op) (G := returnedTensorModel Q X)
    (returnedTensorIso Q X).hom
    (fun _ => (globalModel.obj (op (scheme Q (laurent.op.obj X)))).waldhausen.weq_iso _
      inferInstance)

/-- The real first-row prism intertwines the internal cell and the returned genuine tensor cell.
-/
def returnedPasting (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ((initialCell Q X).trans (returnedMovement Q X)).RelHomotopy
      ((returnedMovement Q X).trans (returnedTensorCell Q X)) := by
  let J := rowTransformationPasting
    (F := globalModel.map (coefficientMap Q X).op)
    (G := globalModel.map (coefficientMap Q X).op)
    (G' := returnedTensorModel Q X) (H := returnedTensorModel Q X)
    (onFunctor (globalModel.map (coefficientMap Q X).op).functor
      (globalUnit (op (scheme Q (laurent.op.obj X)))
        (ParameterLaurentUnit.projectedLaurentScalar Q X))).hom
    (returnedTensorIso Q X).hom (returnedTensorIso Q X).hom (returnedTensorUnit Q X)
    (fun _ => (globalModel.obj (op (scheme Q (laurent.op.obj X)))).waldhausen.weq_iso _
      inferInstance)
    (fun _ => (globalModel.obj (op (scheme Q (laurent.op.obj X)))).waldhausen.weq_iso _
      inferInstance)
    (fun _ => (globalModel.obj (op (scheme Q (laurent.op.obj X)))).waldhausen.weq_iso _
      inferInstance)
    (returnedTensorUnit_weak Q X) (returnedTensorIso_unit Q X)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    rw [Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    rw [Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr <;> rfl

/-- Returning evaluation preserves the whole genuine tensor cell at the original unit time. -/
theorem returnedTensorCell_at (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (returnedTensorCell Q X).at t =
      (rowTransformationSpectrumHomotopy (tensorModelUnit Q X)
        (tensorModelUnit_weak Q X)).at t ≫
        rowLoopMap (evaluationInverseModel (op (scheme Q (laurent.op.obj X)))) :=
  rowTransformationSpectrumHomotopy_postcomp_at (tensorModelUnit Q X)
    (tensorModelUnit_weak Q X)
    (evaluationInverseModel (op (scheme Q (laurent.op.obj X)))) t

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
