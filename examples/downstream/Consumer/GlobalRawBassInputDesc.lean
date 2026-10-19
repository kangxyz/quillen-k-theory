/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRawDesc

/-! A downstream client of the entire original raw descent surface at genuine level zero. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
universe u
namespace Consumer.GlobalRawBassInputDesc
open GlobalBassEvaluation

/-- The actual input loop remains independent of both original raw descent parameters. -/
theorem original_evaluated_square_zero {X Y : Scheme.{u}} (g : X ⟶ Y) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputRawDesc.parameter g) 0 =
      (((GlobalRawBass.inputDescPasting g).toSquare.level 0).comp
        (InputRawDesc.rawInputParameter (Y := Y) 0)).comp
          (InputRawDesc.evaluationInputParameter (Y := Y) 0) :=
  InputRawDesc.whole_native g 0

end Consumer.GlobalRawBassInputDesc
