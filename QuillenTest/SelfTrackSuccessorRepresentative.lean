/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackSuccessorRepresentative

/-! Original successor structure and track time remain independent in the actual cubes. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackSuccessorRepresentative

/-- The original coherent family compares with the original uncurried structure cube pointwise. -/
theorem original_successor_normalized_cube {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    H.genLoopNormalizedSelfTrackCubeSecond (n + 1) (m + 1)
        (loopUncurry (genLoopPostcomp (E.structureMap n) (E.map_point n) p)) =
      transposeGenLoop (0 : Fin (m + 4)) 1 Fin.zero_ne_one
        (loopUncurry (genLoopPostcomp (F.structureMap n) (F.map_point n)
          (genLoopNormalizedSelfTrackCube (m + 1) _ (H.genLoopPath n p)))) :=
  H.genLoopNormalizedSelfTrackCubeSecond_structure n m p

end QuillenTest.SelfTrackSuccessorRepresentative
