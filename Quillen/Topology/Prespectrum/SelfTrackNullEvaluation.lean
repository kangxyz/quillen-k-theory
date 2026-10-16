/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackNull
public import Quillen.Topology.Prespectrum.SelfTrackHomotopyClass

/-!
# Evaluation of the original null-conjugated self-track map

The unchanged original `nullLoopMap` on each actual based cube is precisely
its original null-conjugated track. Uncurrying and the supplied-null class
identity identify its induced finite map with the normalized self-track
operation, retaining both occurrences of the original nullhomotopy.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- The original null-loop map evaluates to its literal original conjugated cube path. -/
theorem Homotopy.nullLoopMap_genLoop_eq (H : Homotopy f f)
    (N : Homotopy f (zeroHom E F)) (n m : ℕ)
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    genLoopPostcomp ((H.nullLoopMap N).map n) ((H.nullLoopMap N).map_point n) p =
      genLoopOfBasedPath ((N.genLoopPath n p).symm.trans
        ((H.genLoopPath n p).trans (N.genLoopPath n p))) := by
  apply GenLoop.ext
  intro z
  apply Path.ext
  funext s
  change ((N.symm.trans (H.trans N)).genLoopPath n p) s z = _
  rw [Homotopy.genLoopPath_trans, Homotopy.genLoopPath_symm, Homotopy.genLoopPath_trans]
  rfl

/-- The actual original null-loop map followed by uncurrying is the finite self-track operation. -/
theorem Homotopy.nullLoopMap_piMap (H : Homotopy f f)
    (N : Homotopy f (zeroHom E F)) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    (loopShiftMulEquiv (x := F.point n) m).symm
        (piMap m ((H.nullLoopMap N).map n) ((H.nullLoopMap N).map_point n) a) =
      H.homotopyClassOperation n m a := by
  refine Quotient.inductionOn a (fun p ↦ ?_)
  change (⟦loopUncurry (genLoopPostcomp ((H.nullLoopMap N).map n)
      ((H.nullLoopMap N).map_point n) p)⟧ : HomotopyGroup.Pi (m + 2)
        (F.space n) (F.point n)) = genLoopSelfTrackClass m _ (H.genLoopPath n p)
  exact (congrArg (fun q ↦ (⟦loopUncurry q⟧ : HomotopyGroup.Pi (m + 2)
    (F.space n) (F.point n))) (H.nullLoopMap_genLoop_eq N n m p)).trans
      (genLoopSelfTrackClass_eq_null_conjugate m _ (H.genLoopPath n p)
        (N.genLoopPath n p)).symm

end Quillen.LoopPrespectrum
