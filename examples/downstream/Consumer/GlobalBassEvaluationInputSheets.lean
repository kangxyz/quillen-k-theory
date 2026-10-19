/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRawPastedNative

/-! An independent level-zero client of the original three-piece raw evaluation input surface. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
universe u
namespace Consumer.GlobalBassEvaluationInputSheets
open GlobalBassEvaluation

/-- The genuine loop input and both original surface parameters survive at degree zero. -/
theorem whole_raw_input_zero {X Y : Scheme.{u}} (g : X ⟶ Y) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (InputRawPastedParameter.parameter g) 0 =
      ((GlobalRawBass.inputComparisonHomotopy g).level 0).comp
        (InputRawPastedNative.inputParameter (Y := Y) 0) :=
  InputRawPastedNative.whole_native g 0

end Consumer.GlobalBassEvaluationInputSheets
