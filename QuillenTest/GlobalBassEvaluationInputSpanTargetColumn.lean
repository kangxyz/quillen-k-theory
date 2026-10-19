/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICEQuillenTest.GlobalBassEvaluationInputSpanTargetColumnE.
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
namespace QuillenTest.GlobalBassEvaluationInputSpanTargetColumn
variable {X Y : Scheme.{u}} (g : X ⟶ Y) (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z =
    Quillen.PerfectComplexes.GlobalRawBass.laurentProjection.app Z)

/-- The complete parameter equality holds at every original evaluation time. -/
theorem whole (t : unitInterval) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputSpanParameterNodes.nodes g k hk) ((edge (k := 7) 3 4) t) =
        InputRawChartProductNodes.parameter g k hk (t, 1) :=
  InputSpanTargetColumn.column_parameter g k hk t

/-- The cut node retains its entire original reference isomorphism. -/
theorem initial_node : InputSpanParameterNodes.nodes g k hk 3 =
    InputRawChartProductNodes.nodes g k hk 4 :=
  InputSpanTargetColumn.column_initial_node g k hk

/-- Both original full anchored vertices occur in the fixed product column. -/
theorem both_nodes (i : Fin 2) :
    InputRawChartProductNodes.nodes g k hk ((Quillen.SimplexGrid.columnFace 1 4 4).toOrderHom i) =
      InputSpanParameterNodes.nodes g k hk (InputSpanTargetColumn.projectionFace.toOrderHom i) :=
  InputSpanTargetColumn.column_nodes g k hk i

end QuillenTest.GlobalBassEvaluationInputSpanTargetColumn
