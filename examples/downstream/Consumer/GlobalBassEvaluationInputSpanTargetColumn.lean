/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICEConsumer.GlobalBassEvaluationInputSpanTargetColumnE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanTargetColumn

/-! Complete anchored projection-column equality and its whole parameter family. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.GlobalBassEvaluation
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Consumer.GlobalBassEvaluationInputSpanTargetColumn
variable {X Y : Scheme.{u}} (g : X ⟶ Y) (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z =
    Quillen.PerfectComplexes.GlobalRawBass.laurentProjection.app Z)

/-- The complete parameter equality holds at every original evaluation time. -/
theorem whole (t : unitInterval) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputSpanParameterNodes.nodes g k hk) ((edge (k := 7) 3 4) t) =
        InputRawChartProductNodes.parameter g k hk (t, 1) :=
  InputSpanTargetColumn.column_parameter g k hk t

end Consumer.GlobalBassEvaluationInputSpanTargetColumn
