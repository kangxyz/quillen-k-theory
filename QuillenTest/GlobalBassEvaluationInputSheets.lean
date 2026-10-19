/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRawPastedNative
import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartSquareParameter

/-! Regression checks for the complete mixed chart faces and three-piece raw input surface. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationInputSheets
open GlobalBassEvaluation GlobalSectionChangeIndex Quillen.NativePathCells
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Every terminal product node keeps its entire actual projected reference anchor. -/
theorem inverse_terminal_nodes (i : Fin 5) :
    InputRawChartProductNodes.nodes g minus GlobalRawBass.minus_projection
      ((Quillen.SimplexGrid.rowFace 1 4 1).toOrderHom i) =
      InputRawChartRows.projectedNode g minus GlobalRawBass.minus_projection
        (InputRawChartRows.squareNodes g minus i) :=
  InputRawChartProductNodes.terminal_nodes g minus GlobalRawBass.minus_projection i

/-- The positive product and entire raw descent meet at the original full-time nerve edge. -/
theorem positive_full_seam (r : unitInterval) :
    InputRawChartProductNodes.parameter g plus GlobalRawBass.plus_projection (1, r) =
      InputRawDesc.parameter g (r, 0) :=
  InputRawChartProductNodes.plus_attachment g r

/-- The middle quarter is the original raw descent parameter, including both shared seams. -/
theorem middle_quarter (r s : unitInterval) :
    InputRawPastedParameter.parameter g (r, upper (lower s)) =
      InputRawDesc.parameter g (r, s) :=
  InputRawPastedParameter.parameter_middle g r s

/-- The inverse quarter preserves the actual reversed evaluation coordinate. -/
theorem inverse_quarter (r s : unitInterval) :
    InputRawPastedParameter.parameter g (r, upper (upper s)) =
      InputRawChartProductNodes.parameter g minus GlobalRawBass.minus_projection
        (unitInterval.symm s, r) :=
  InputRawPastedParameter.parameter_upper g r s

/-- The entire two-time compact family is the original input homotopy after span evaluation. -/
theorem whole_original_family (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputRawPastedParameter.parameter g) n = InputRawPastedNative.nativeFamily g n :=
  InputRawPastedNative.whole_native g n

/-- The entire chart source edge remains the original unpaused scalar path. -/
theorem inverse_chart_source (s : unitInterval) :
    InputChartSquareParameter.minusParameter g (0, s) =
      InputChartSquareParameter.edge g minus GlobalRawBass.minus_projection 0 6 s :=
  InputChartSquareParameter.parameter_zero g minus GlobalRawBass.minus_projection s

end QuillenTest.GlobalBassEvaluationInputSheets
