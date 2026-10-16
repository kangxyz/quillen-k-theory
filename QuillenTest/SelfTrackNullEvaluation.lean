/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackNullEvaluation

/-! # Original null-loop representative and degree-one finite evaluation -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackNullEvaluation

/-- The exact original map retains its original self-track and both original null paths. -/
theorem original_null_loop_cube {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (N : Homotopy f (zeroHom E F)) (n m : ℕ)
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    genLoopPostcomp ((H.nullLoopMap N).map n) ((H.nullLoopMap N).map_point n) p =
      genLoopOfBasedPath ((N.genLoopPath n p).symm.trans
        ((H.genLoopPath n p).trans (N.genLoopPath n p))) :=
  H.nullLoopMap_genLoop_eq N n m p

/-- The original map evaluation already holds at input degree one. -/
theorem original_degree_one_evaluation {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (N : Homotopy f (zeroHom E F)) (n : ℕ)
    (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    (loopShiftMulEquiv (x := F.point n) 0).symm
        (piMap 0 ((H.nullLoopMap N).map n) ((H.nullLoopMap N).map_point n) a) =
      H.homotopyClassOperation n 0 a :=
  H.nullLoopMap_piMap N n 0 a

end QuillenTest.SelfTrackNullEvaluation
