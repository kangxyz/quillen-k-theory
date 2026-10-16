/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackCoordinateChange

/-! The actual swapped-input, restored-output representative has the original higher class. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackCoordinateChange

/-- Changing the normalization coordinate preserves the class of the actual original H-track. -/
theorem original_second_normalization_class {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    (⟦H.genLoopNormalizedSelfTrackCubeSecond n m p⟧ :
      HomotopyGroup.Pi (m + 3) (F.space n) (F.point n)) =
        genLoopSelfTrackClass (m + 1) _ (H.genLoopPath n p) :=
  H.genLoopNormalizedSelfTrackCubeSecond_class n m p

/-- The same time slice of the same H-family retains the exact original coordinate swap. -/
theorem original_transposed_track_time {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) (t : unitInterval) :
    H.genLoopPath n (transposeGenLoop 0 1 Fin.zero_ne_one p) t =
      transposeGenLoop 0 1 Fin.zero_ne_one (H.genLoopPath n p t) :=
  H.genLoopPath_transpose n (m + 2) 0 1 Fin.zero_ne_one p t

end QuillenTest.SelfTrackCoordinateChange
