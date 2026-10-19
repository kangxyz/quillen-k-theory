/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedStrictification
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedReturnedStrictification

/-! # Genuine tensor-started recursion retains all original stages and whole unit times -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.KTheory.Bass Quillen.PerfectComplexes Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace QuillenTest.ParameterTensorReturnedStrictification
open GlobalSectionChangeIndex

/-- Every ambient stage retains the original normalized boundary after tensor-started recursion. -/
theorem ambient_forward (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    ParameterTensorEvaluationRow.strictifiedNormalizedForward Q i X =
      SchemeModelRowSeed.normalizedBoundary (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) i X :=
  ParameterTensorEvaluationRow.strictifiedNormalizedForward_eq Q i X

/-- The actual supported tensor itself supplies the corresponding all-stage equality. -/
theorem supported_forward {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    ParameterTensorSupportedRow.strictifiedNormalizedForward f i X =
      SchemeModelRowSeed.normalizedBoundary (ParameterModels.supported f)
        (ParameterLaurentTrack.supportedUnit f)
        (ParameterLaurentTrack.supportedUnit_naturality f) i X :=
  ParameterTensorSupportedRow.strictifiedNormalizedForward_eq f i X

/-- Unit time is unchanged on the complete ambient spectrum map at any Bass stage. -/
theorem ambient_cell_time (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (ParameterTensorEvaluationRow.strictifiedIteratedCell Q i X).at t =
      (SchemeModelRowSeed.cell (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q)
        (ParameterLaurentUnit.ambientUnit_naturality Q) i X).at t :=
  congrArg (fun H => H.at t) (ParameterTensorEvaluationRow.strictifiedIteratedCell_eq Q i X)

/-- The supported cell retains the entire same-time map, including its zeroth loop level. -/
theorem supported_cell_time {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (i : ℕ) (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (ParameterTensorSupportedRow.strictifiedIteratedCell f i X).at t =
      (SchemeModelRowSeed.cell (ParameterModels.supported f)
        (ParameterLaurentTrack.supportedUnit f)
        (ParameterLaurentTrack.supportedUnit_naturality f) i X).at t :=
  congrArg (fun H => H.at t) (ParameterTensorSupportedRow.strictifiedIteratedCell_eq f i X)

end QuillenTest.ParameterTensorReturnedStrictification
