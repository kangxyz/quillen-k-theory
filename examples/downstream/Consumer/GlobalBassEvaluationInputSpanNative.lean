/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanParameterWhole
import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanTargetNodes

/-! Independent clients of the original full span family and complete target anchor. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalBassEvaluationInputSpanNative
open GlobalBassEvaluation
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Both scalar coordinates and the original loop input persist in the entire zero level. -/
theorem span_degree_zero :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputSpanParameterWord.parameter g) 0 =
    ((GlobalRawBass.comparison X).map 0).comp
      (((inputSpanHomotopy g).level 0).comp
        ⟨fun z => (z.1.1, HomotopyPushout.cylinder
          (sectionMap (projection.app Y)) (sectionMap (projection.app Y)) 0 (z.1.2, z.2)),
          by fun_prop⟩) :=
  InputSpanParameterWhole.native g 0

/-- The positive target column is attached through its complete original reference node. -/
theorem positive_terminal_node :
    InputSpanParameterNodes.nodes g plus GlobalRawBass.plus_projection 4 =
      InputRawChartProductNodes.nodes g plus GlobalRawBass.plus_projection 9 :=
  InputSpanTargetNodes.column_terminal_node g plus GlobalRawBass.plus_projection

end Consumer.GlobalBassEvaluationInputSpanNative
