/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedForward
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedReturnedForward
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedReturnedCounit

/-! # Genuine returned tensor forward legs on the literal two parameter Models

The initial face is the independently normalized genuine tensor cell followed by the
original boundary. The last face is the proper-row forward, with the specified null.
Both original spectrum degree zero and every positive degree occur in the quantifier.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.ParameterTensorReturnedForward

/-- The positive first-row prism retains its independent row and original unit coordinates. -/
theorem ambient_prism_positive (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ)
    (x : (prespectrum ((ParameterModels.ambient Q).obj X)).space (k + 1))
    (t s : unitInterval) :
    Path.toContinuousMap
      ((ParameterTensorEvaluationRow.returnedPasting Q X).level (k + 1) (0, (t, x))) s =
    Path.toContinuousMap
      (((ParameterTensorEvaluationRow.initialCell Q X).trans
        (ParameterTensorEvaluationRow.returnedMovement Q X)).level (k + 1) (t, x)) s :=
  congrArg (fun y => Path.toContinuousMap y s)
    (((ParameterTensorEvaluationRow.returnedPasting Q X).level (k + 1)).apply_zero (t, x))

/-- Degree zero retains the original input-loop coordinate independently of the row coordinate. -/
theorem ambient_prism_zero (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (x : (prespectrum ((ParameterModels.ambient Q).obj X)).space 0)
    (t a s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      ((ParameterTensorEvaluationRow.returnedPasting Q X).level 0 (0, (t, x))) a) s =
    Path.toContinuousMap (Path.toContinuousMap
      (((ParameterTensorEvaluationRow.initialCell Q X).trans
        (ParameterTensorEvaluationRow.returnedMovement Q X)).level 0 (t, x)) a) s :=
  congrArg (fun y => Path.toContinuousMap (Path.toContinuousMap y a) s)
    (((ParameterTensorEvaluationRow.returnedPasting Q X).level 0).apply_zero (t, x))

/-- The ambient comparison starts at the actual genuine tensor cup/boundary operation. -/
theorem ambient_original_face (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (prespectrum ((ParameterModels.ambient Q).obj X)).space n) :
    (ParameterTensorEvaluationRow.returnedNormalizedForwardHomotopy Q X).level n (0, x) =
      (ParameterTensorEvaluationRow.returnedNormalizedCupBoundary Q X).map n x :=
  (ParameterTensorEvaluationRow.returnedNormalizedForwardHomotopy Q X).at_zero n x

/-- Its final face is the original proper-row forward, with no target inverse. -/
theorem ambient_original_forward (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (prespectrum ((ParameterModels.ambient Q).obj X)).space n) :
    (ParameterTensorEvaluationRow.returnedNormalizedForwardHomotopy Q X).level n (1, x) =
      (SchemeModelRowSeed.forward (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q)
        (ParameterLaurentUnit.ambientUnit_naturality Q) 0 X).map n x :=
  (ParameterTensorEvaluationRow.returnedNormalizedForwardHomotopy Q X).at_one n x

/-- The supported comparison starts at the actual internally supported tensor operation. -/
theorem supported_original_face {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (prespectrum ((ParameterModels.supported f).obj X)).space n) :
    (ParameterTensorSupportedRow.returnedNormalizedForwardHomotopy f X).level n (0, x) =
      (ParameterTensorSupportedRow.returnedNormalizedCupBoundary f X).map n x :=
  (ParameterTensorSupportedRow.returnedNormalizedForwardHomotopy f X).at_zero n x

/-- Its target is the same specified supported proper-row forward at every spectrum degree. -/
theorem supported_original_forward {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (prespectrum ((ParameterModels.supported f).obj X)).space n) :
    (ParameterTensorSupportedRow.returnedNormalizedForwardHomotopy f X).level n (1, x) =
      (SchemeModelRowSeed.forward (ParameterModels.supported f)
        (ParameterLaurentTrack.supportedUnit f)
        (ParameterLaurentTrack.supportedUnit_naturality f) 0 X).map n x :=
  (ParameterTensorSupportedRow.returnedNormalizedForwardHomotopy f X).at_one n x

/-- On the literal supported parameter, reevaluation recovers the specified whole movement. -/
theorem supported_original_movement {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (K : (ParameterModels.supported f).obj X) :
    (SupportedTensorEvaluation.evaluationModel
        (X := op (ParameterTensorSupportedRow.pair f (laurent.op.obj X)).obj.right)
        (ParameterTensorSupportedRow.pair f (laurent.op.obj X)).obj.hom).functor.map
        ((SupportedTensorEvaluation.returnedTensorIso
          (ParameterTensorSupportedRow.coefficientPair f X)).hom.app K) ≫
      (SupportedTensorEvaluation.returnedTensorEvaluationIso
        (ParameterTensorSupportedRow.coefficientPair f X)).hom.app K =
      (SupportedTensorEvaluation.internalTensorModelIso
        (ParameterTensorSupportedRow.coefficientPair f X)).hom.app K :=
  NatTrans.congr_app (SupportedTensorEvaluation.returnedTensorIso_evaluation
    (ParameterTensorSupportedRow.coefficientPair f X)) K

end QuillenTest.ParameterTensorReturnedForward
