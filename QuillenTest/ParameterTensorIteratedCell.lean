/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorIteratedCell
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedIteratedCell
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorFirstBassCell

/-! # Actual finite tensor-cell iteration retains its genuine initial and first stages

These regressions compare the recursively constructed ambient cell with the independently
checked first Bass cell, and retain the actual supported initial row at every spectrum level.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.ParameterTensorIteratedCell

/-- Recursive descent at the first Bass stage agrees with the independent first-stage cell. -/
theorem first_stage (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (ParameterTensorEvaluationRow.iteratedCell Q 1 X).at t =
      (ParameterTensorEvaluationRow.firstBassCell Q X).at t := by
  rw [ParameterTensorEvaluationRow.iteratedCell_at_eq,
    ParameterTensorEvaluationRow.firstBassCell_at_eq]
  rfl

/-- Supported iteration retains the genuine supported initial row, at every spectrum level. -/
theorem supported_initial_level {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) :
    (ParameterTensorSupportedRow.iteratedCell f 0 X).level n =
      (ParameterTensorSupportedRow.initialCell f X).level n :=
  ParameterTensorSupportedRow.iteratedCell_zero_level f X n

end QuillenTest.ParameterTensorIteratedCell
