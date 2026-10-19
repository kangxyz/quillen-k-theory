/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanParameterPaths
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanTargetColumn
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputTargetFace
public import Quillen.Aglib.Topology.Path.EvaluationFactorExtraction

/-!
# The complete actual-composite target seam of the input-span parameter

The original evaluation column and polynomial square are recovered from their entire top
chart. The five resulting leaves agree with the original raw pasted target word, including
both normalization halves and all nested concatenation coordinates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanParameterTarget
open GlobalSectionChangeIndex InputSpanParameterWord
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The exact first half of either original chart is its complete evaluation column. -/
theorem chart_first (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)
    (s : unitInterval) :
    chartSwap g k hk (Path.CarrierHalfPaths.lower s, 1) =
      InputRawChartProductNodes.parameter g k hk (s, 1) :=
  (chart_initial g k hk s).trans (InputSpanTargetColumn.column_parameter g k hk s)

/-- The complete five-leaf actual target is the original three-sheet raw pasted boundary. -/
theorem actual_top (s : unitInterval) :
    actualTop g s = InputRawPastedParameter.parameter g (1, s) := by
  change ((firstPlus g).trans
    (((lastPlus g).trans ((overlapTop g).trans (lastMinus g).symm)).trans
      (firstMinus g).symm)) s =
    ((Quillen.ScalarRectangle.rowHomotopy
      (Quillen.ScalarRectangle.swap (InputRawPastedParameter.plusSheet g))).trans
      ((Quillen.ScalarRectangle.rowHomotopy
        (Quillen.ScalarRectangle.swap (InputRawPastedParameter.tailParameter g))).cast _ _)) (s, 1)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact chart_first g plus GlobalRawBass.plus_projection _
  · change _ = ((Quillen.ScalarRectangle.rowHomotopy
        (Quillen.ScalarRectangle.swap (InputRawDesc.parameter g))).trans
      ((Quillen.ScalarRectangle.rowHomotopy
        (Quillen.ScalarRectangle.swap (InputRawPastedParameter.minusSheet g))).cast _ _)) (_, 1)
    rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split
    · exact middle_top g _
    · exact chart_first g minus GlobalRawBass.minus_projection (unitInterval.symm _)

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanParameterTarget

namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanParameterSeams
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The entire target face ends at the original actual-composite input-span boundary. -/
theorem target (s : unitInterval) :
    InputTargetFace.parameter g (1, s) = InputSpanParameterWord.parameter g (1, s) := by
  rw [InputSpanParameterWord.parameter_one]
  exact (Quillen.ScalarRectangle.concatFirst_one
    (InputMixedDesc.postSquareParameter g) (InputRawPastedParameter.parameter g)
    (InputRawPastedSeam.seam g) s).trans (InputSpanParameterTarget.actual_top g s).symm

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanParameterSeams
