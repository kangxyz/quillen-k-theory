/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartPrism

/-! A downstream client retains the original normalization prism at genuine level zero. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalBassEvaluationInputChartPrism
open GlobalBassEvaluation GlobalSectionChangeIndex

/-- The actual inverse-chart bridge keeps the loop coordinate separate from all three times. -/
theorem original_inverse_prism_zero {X Y : Scheme.{u}} (g : X ⟶ Y) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputChartReference.prismParameter g minus GlobalRawBass.minus_projection) 0 =
      ((boundedFlatNormalizedCompTrackComparison
        (minus.app X) (projection.app X)).level 0).toContinuousMap.comp
          (InputNormalizationPrism.movingParameter g 0) :=
  InputChartReference.prism_whole_native g minus GlobalRawBass.minus_projection 0

end Consumer.GlobalBassEvaluationInputChartPrism
