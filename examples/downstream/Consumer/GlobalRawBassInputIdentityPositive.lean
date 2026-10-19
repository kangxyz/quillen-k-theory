/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityPositiveFactor
/-! Independent consumption of the exact positive support of the fixed global identity. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
universe u
namespace Consumer.GlobalRawBassInputIdentityPositive

/-- The original seed factors with no extra comparison or filler premise. -/
theorem original_seed (X : Scheme.{u}) : InputIdentityPositive.seed X ≫
    parameterLoopingMap (InputIdentityPositive.inclusion X) = transition X :=
  InputIdentityPositive.seed_factor X

/-- Every positive-cone point has the same fixed original whole identity image. -/
theorem whole_cone (X : Scheme.{u}) (n : ℕ) (r : unitInterval)
    (x : (mappingCone (InputIdentityPositive.chart X)).space n) :
    (InputIdentityPositive.inclusion X).map n
      ((InputIdentityPositive.coneHomotopy X).level n (r, x)) =
    (InputIdentity.coneHomotopy X).level n
      (r, (InputIdentityPositive.inclusion X).map n x) :=
  InputIdentityPositive.coneHomotopy_factor X n r x

end Consumer.GlobalRawBassInputIdentityPositive
