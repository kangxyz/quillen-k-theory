/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrack
public import Quillen.Topology.Prespectrum.HomotopyLoop

/-!
# The actual self-track on one sphere representative

Currying a whole prespectrum homotopy after an original based cube retains the original
homotopy time and every cube boundary. Vanishing in the one-higher finite degree contracts
that particular self-track, even when its sphere represents a nonzero component. Postcomposing
and conjugating by the prescribed original null path then gives a boundary-relative nullhomotopy
of its actual loop-valued sphere. No global relative homotopy of prespectrum maps is chosen.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}}

/-- The whole original level homotopy, evaluated on the same original based cube. -/
def Homotopy.genLoopPath {f g : E ⟶ F} (H : Homotopy f g) (n : ℕ)
    {m : ℕ} (p : GenLoop (Fin m) (E.space n) (E.point n)) :
    Path (genLoopPostcomp (f.map n) (f.map_point n) p)
      (genLoopPostcomp (g.map n) (g.map_point n) p) :=
  genLoopPathOfHomotopyRel (genLoopPostcompHomotopy (f.map_point n) (g.map_point n)
    (H.levelHomotopy n).toHomotopy (H.at_point n) p)

/-- Currying does not change either original coordinate. -/
@[simp] theorem Homotopy.genLoopPath_apply {f g : E ⟶ F} (H : Homotopy f g) (n : ℕ)
    {m : ℕ} (p : GenLoop (Fin m) (E.space n) (E.point n))
    (s : unitInterval) (z : Fin m → unitInterval) :
    H.genLoopPath n p s z = H.level n (s, p z) := rfl

/-- Reversal retains precisely the original reversed path in the based-cube space. -/
theorem Homotopy.genLoopPath_symm {f g : E ⟶ F} (H : Homotopy f g) (n : ℕ)
    {m : ℕ} (p : GenLoop (Fin m) (E.space n) (E.point n)) :
    H.symm.genLoopPath n p = (H.genLoopPath n p).symm := by
  ext s z
  rfl

/-- Concatenation keeps its original interval halves after evaluation on a sphere. -/
theorem Homotopy.genLoopPath_trans {f g h : E ⟶ F}
    (H : Homotopy f g) (K : Homotopy g h) (n : ℕ)
    {m : ℕ} (p : GenLoop (Fin m) (E.space n) (E.point n)) :
    (H.trans K).genLoopPath n p = (H.genLoopPath n p).trans (K.genLoopPath n p) := by
  ext s z
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (s, p z) = _
  rw [ContinuousMap.HomotopyRel.trans_apply, Path.trans_apply]
  split <;> rfl

/-- The self-track on this particular original sphere is trivial when its one-higher obstruction
vanishes. The sphere itself need not be null. -/
theorem Homotopy.genLoopPath_homotopic_refl {f : E ⟶ F} (H : Homotopy f f)
    (n m : ℕ) (hF : Subsingleton (HomotopyGroup.Pi (m + 2) (F.space n) (F.point n)))
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    (H.genLoopPath n p).Homotopic
      (Path.refl (genLoopPostcomp (f.map n) (f.map_point n) p)) :=
  genLoop_selfTrack_homotopic_refl m hF _ _

/-- The original null-conjugated loop on a specified sphere contracts relative to its entire
boundary. Both occurrences of the supplied null path are retained in the argument. -/
theorem Homotopy.nullLoopMap_genLoop_homotopic_const {f : E ⟶ F}
    (H : Homotopy f f) (j : F ⟶ G)
    (N : Homotopy (f ≫ j) (zeroHom E G)) (n m : ℕ)
    (hF : Subsingleton (HomotopyGroup.Pi (m + 2) (F.space n) (F.point n)))
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    GenLoop.Homotopic
      (genLoopPostcomp (((H.postcomp j).nullLoopMap N).map n)
        (((H.postcomp j).nullLoopMap N).map_point n) p) GenLoop.const := by
  let a := genLoopPostcomp ((f ≫ j).map n) ((f ≫ j).map_point n) p
  let P : Path a a := (H.postcomp j).genLoopPath n p
  let Q : Path a (GenLoop.const : GenLoop (Fin (m + 1)) (G.space n) (G.point n)) :=
    N.genLoopPath n p
  have hP : P.Homotopic (Path.refl a) := by
    obtain ⟨K⟩ := H.genLoopPath_homotopic_refl n m hF p
    refine ⟨{
      toFun rs := genLoopPostcomp (j.map n) (j.map_point n) (K rs)
      continuous_toFun :=
        (genLoopPostcompContinuousMap (j.map n) (j.map_point n)).continuous.comp K.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro s
      apply GenLoop.ext
      intro z
      exact congrArg (fun q => (j.map n) (q z)) (K.apply_zero s)
    · intro s
      apply GenLoop.ext
      intro z
      exact congrArg (fun q => (j.map n) (q z)) (K.apply_one s)
    · intro r s hs
      apply GenLoop.ext
      intro z
      rcases hs with hs | hs
      · subst s
        change (j.map n) (K (r, 0) z) = (j.map n) (H.level n (0, p z))
        rw [K.source]
        exact congrArg (j.map n) (H.at_zero n (p z)).symm
      · have hs : s = 1 := hs
        subst s
        change (j.map n) (K (r, 1) z) = (j.map n) (H.level n (1, p z))
        rw [K.target]
        exact congrArg (j.map n) (H.at_one n (p z)).symm
  have hQ : (Q.symm.trans (P.trans Q)).Homotopic (Path.refl GenLoop.const) :=
    ((Path.Homotopic.refl Q.symm).hcomp
      (hP.hcomp (Path.Homotopic.refl Q))).trans
        (((Path.Homotopic.refl Q.symm).hcomp (Path.Homotopic.refl_trans Q)).trans
          (Path.Homotopic.symm_trans Q))
  have he : genLoopPostcomp (((H.postcomp j).nullLoopMap N).map n)
      (((H.postcomp j).nullLoopMap N).map_point n) p =
      genLoopOfBasedPath (Q.symm.trans (P.trans Q)) := by
    apply GenLoop.ext
    intro z
    apply Path.ext
    funext s
    change ((N.symm.trans ((H.postcomp j).trans N)).genLoopPath n p) s z = _
    rw [Homotopy.genLoopPath_trans, Homotopy.genLoopPath_symm,
      Homotopy.genLoopPath_trans]
    rfl
  rw [he]
  simpa only [genLoopOfBasedPath_refl] using genLoopOfBasedPath_homotopic hQ

end Quillen.LoopPrespectrum
