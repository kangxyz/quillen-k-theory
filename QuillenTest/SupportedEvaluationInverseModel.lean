/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationInverseModel

/-! # Original supported evaluation and its chosen-zero exact inverse -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.SupportedTensorEvaluation
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
universe u
namespace QuillenTest.SupportedEvaluationInverseModel
variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- The equivalence has the already prescribed evaluation as its literal forward functor. -/
theorem forward_unchanged :
    (SupportedTensorEvaluation.evaluationModelEquivalence j).functor =
      (SupportedTensorEvaluation.evaluationModel j).functor := rfl

/-- The backward map preserves the actual supported section zero. -/
theorem backward_zero :
    (evaluationInverseModel j).functor.obj
        (Quillen.Waldhausen.IteratedS.modelOf
          (boundedFlatPerfectSupportedWaldhausen j)).waldhausen.zero =
      (supportedModel j).waldhausen.zero :=
  (evaluationInverseModel j).zero

end QuillenTest.SupportedEvaluationInverseModel
