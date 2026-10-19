/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputTargetFace
import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputConeSource

/-! Independent clients of the entire original target face and literal strict cone input. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
universe u
namespace Consumer.GlobalBassEvaluationInputTarget
open GlobalBassEvaluation
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Both target-face coordinates and the genuine original level-zero input are unchanged. -/
theorem target_degree_zero :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputTargetFace.parameter g) 0 =
      ((InputComparisonTracks.target g).level 0).comp
        (InputTargetFace.cylinderParameter (Y := Y) 0) :=
  InputTargetFace.whole_native g 0

/-- The whole original strict cone-input composite is exactly the direct source square map. -/
theorem strict_source_cone :
    InputConeSource.strictConeMap g ≫ coneEvaluation X = InputConeSource.directConeMap g :=
  InputConeSource.strict_comp_evaluation g

end Consumer.GlobalBassEvaluationInputTarget
