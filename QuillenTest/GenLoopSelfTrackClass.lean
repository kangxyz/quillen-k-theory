/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackClass
public import Quillen.Topology.Prespectrum.SelfTrackRepresentative

/-! Original prespectrum tracks retain their finite higher obstruction class. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true

open CategoryTheory
open Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.GenLoopSelfTrackClass

/-- Equality of the retained classes detects relative homotopy of the actual evaluated tracks. -/
theorem original_tracks_detected {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H K : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    genLoopSelfTrackClass m _ (H.genLoopPath n p) =
      genLoopSelfTrackClass m _ (K.genLoopPath n p) ↔
        (H.genLoopPath n p).Homotopic (K.genLoopPath n p) :=
  genLoopSelfTrackClass_eq_iff m _ _ _

/-- The old vanishing hypothesis annihilates the retained class without changing the track. -/
theorem original_vanishing_class {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (hF : Subsingleton (HomotopyGroup.Pi (m + 2) (F.space n) (F.point n)))
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    genLoopSelfTrackClass m _ (H.genLoopPath n p) = 1 :=
  (genLoopSelfTrackClass_eq_one_iff m _ _).mpr (H.genLoopPath_homotopic_refl n m hF p)

end QuillenTest.GenLoopSelfTrackClass
