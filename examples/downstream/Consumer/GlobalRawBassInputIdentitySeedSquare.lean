/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentitySeedSquare

/-! Independent consumption of the actual whole raw transition identity square. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open scoped unitInterval
universe u
namespace Consumer.GlobalRawBassInputIdentitySeedSquare
variable (X : Scheme.{u})

/-- An independent client receives the actual square with all original selected boundaries. -/
def actualSquare : (transitionInputHomotopy (𝟙 X)).Square
    (coneSquareIdentityTrack (transition X))
    (Homotopy.precomp (transition X) (InputIdentity.mapHomotopy X))
    ((boundedFlatPerfectPrespectrumIdHomotopy X).postcomp (transition X)) :=
  InputIdentitySeedSquare.square X

/-- The original input transition remains the complete bottom face at every loop point. -/
theorem original_transition (n : ℕ) (s v : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    Path.toContinuousMap ((actualSquare X).level n (0, (s, x))) v =
      Path.toContinuousMap ((transitionInputHomotopy (𝟙 X)).level n (s, x)) v :=
  congrArg (fun p ↦ Path.toContinuousMap p v) ((actualSquare X).at_zero n s x)

/-- The complete target identity face still uses the fixed whole raw map identity. -/
theorem fixed_map_identity (n : ℕ) (r v : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    Path.toContinuousMap ((actualSquare X).level n (r, (0, x))) v =
      Path.toContinuousMap ((InputIdentity.mapHomotopy X).level n
        (r, (transition X).map n x)) v :=
  congrArg (fun p ↦ Path.toContinuousMap p v) ((actualSquare X).left n r x)

end Consumer.GlobalRawBassInputIdentitySeedSquare
