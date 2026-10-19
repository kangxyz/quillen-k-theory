/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputPositiveFactor
import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputPositiveSeed

/-! Independent clients of the exact supported input law and the original objectwise seed law. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.PerfectComplexes
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalBassEvaluationInputPositive
open GlobalBassEvaluation
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Even degree-zero positive loops recover the fixed whole input homotopy at every time. -/
theorem degree_zero_input (r s : unitInterval)
    (γ : (parameterLooping (mappingCone (InputPositive.strictChart Y))).space 0) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map 0
      (Path.toContinuousMap ((InputPositive.stepHomotopy g).level 0 (r, γ)) s) =
      Path.toContinuousMap ((InputNaturality.stepHomotopy g).level 0
        (r, (parameterLoopingMap (InputPositive.strictInclusion Y)).map 0 γ)) s :=
  InputPositive.stepHomotopy_factor g 0 r s γ

/-- The actual seed law has exact positive support for arbitrary objects and both times. -/
theorem whole_objectwise_seed (n : ℕ) (r s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op X)).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (Path.toContinuousMap ((InputPositive.seedHomotopy X).level n (r, x)) s) =
      Path.toContinuousMap ((GlobalBassEvaluation.seedHomotopy X).level n (r, x)) s :=
  InputPositive.seedHomotopy_factor X n r s x

end Consumer.GlobalBassEvaluationInputPositive
