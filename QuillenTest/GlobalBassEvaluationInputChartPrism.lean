/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartPrism

/-! Regression checks for complete chart attachments and the original three-clock bridge prism. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationInputChartPrism
open GlobalBassEvaluation GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual positive chart attaches every original X node with its full anchor. -/
theorem positive_pre_node (i : Fin 5) :
    InputChartReference.preNode g plus GlobalRawBass.plus_projection i =
      InputMixedDesc.preNode g
        (InputChartSimplex.chartNodes X (plus.app X) (GlobalRawBass.plus_projection X) i) :=
  InputChartReference.pre_nodes g plus GlobalRawBass.plus_projection i

/-- Every point of the actual inverse chart uses its original mixed descent characteristic map. -/
theorem inverse_pre_characteristic (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.preNode g minus GlobalRawBass.minus_projection) z =
    CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g)
      (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)
        (StdSimplex.map InputChartSimplex.minusFace.toOrderHom z)) :=
  InputChartReference.minus_pre_parameter g z

/-- The whole actual positive prism keeps all three independent native parameters. -/
theorem positive_prism_native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputChartReference.prismParameter g plus GlobalRawBass.plus_projection) n =
      ((boundedFlatNormalizedCompTrackComparison
        (plus.app X) (projection.app X)).level n).toContinuousMap.comp
          (InputNormalizationPrism.movingParameter g n) :=
  InputChartReference.prism_whole_native g plus GlobalRawBass.plus_projection n

/-- The converted inverse row is the entire prescribed raw normalization face. -/
theorem inverse_converted_characteristic (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.prismNode g minus GlobalRawBass.minus_projection)
      (Quillen.SimplexGrid.parameter.{u} 1 2 (StdSimplex.single 1, z)) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.rawNode g minus GlobalRawBass.minus_projection)
      (StdSimplex.map InputRectangleNodes.preNormalizationFace.toOrderHom z) :=
  InputChartReference.prism_raw_parameter g minus GlobalRawBass.minus_projection z

end QuillenTest.GlobalBassEvaluationInputChartPrism
