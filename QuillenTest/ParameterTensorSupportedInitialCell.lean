/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedInitialCell
import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientOperation
import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientForget

/-! # Actual supported tensor-cell boundary regression

The independently constructed tensor cell has both original row endpoints, uniformly in its
unit time and every finite S-input. The endpoint-relative comparison retains these same row
endpoints uniformly in the independent comparison time, including the degree-zero input loop.
-/
noncomputable section
open AlgebraicGeometry Opposite Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.ParameterTensorSupportedRow
open Quillen.PerfectComplexes.SupportedTensorEvaluation
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.ParameterTensorSupportedInitialCell

/-- Both original tensor-row zero faces persist under actual parameter evaluation. -/
theorem independent_row_endpoints {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (k : ℕ)
    (t : unitInterval) (x : stageSpace k ((ParameterModels.supported f).obj X)) :
    tensorCellRealization (coefficientPair f X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) k (0, (t, x)) =
        stagePoint (k + 1)
          (modelOf (boundedFlatPerfectSupportedWaldhausen (pair f (laurent.op.obj X)).obj.hom)) ∧
    tensorCellRealization (coefficientPair f X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) k (1, (t, x)) =
        stagePoint (k + 1)
          (modelOf
            (boundedFlatPerfectSupportedWaldhausen (pair f (laurent.op.obj X)).obj.hom)) := by
  constructor
  · rw [← tensorCell_succ (coefficientPair f X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) k t 0 x]
    exact Path.source _
  · rw [← tensorCell_succ (coefficientPair f X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) k t 1 x]
    exact Path.target _

/-- The genuine comparison prism keeps the original zero row for every unit/comparison time. -/
theorem prism_zero_row {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (k : ℕ)
    (r t : unitInterval) (x : stageSpace k ((ParameterModels.supported f).obj X)) :
    Path.toContinuousMap ((firstRowPasting f X).level (k + 1) (r, (t, x))) 0 =
      stagePoint (k + 1)
        (modelOf (boundedFlatPerfectSupportedWaldhausen (pair f (laurent.op.obj X)).obj.hom)) :=
  Path.source _

/-- Degree zero retains the arbitrary original input-loop coordinate in the same prism. -/
theorem prism_zero_level_row {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ)
    (r t a : unitInterval)
    (γ : Path (stagePoint 0 ((ParameterModels.supported f).obj X))
      (stagePoint 0 ((ParameterModels.supported f).obj X))) :
    Path.toContinuousMap
      (Path.toContinuousMap ((firstRowPasting f X).level 0 (r, (t, γ))) a) 0 =
      stagePoint 1
        (modelOf (boundedFlatPerfectSupportedWaldhausen (pair f (laurent.op.obj X)).obj.hom)) :=
  Path.source _

end QuillenTest.ParameterTensorSupportedInitialCell
