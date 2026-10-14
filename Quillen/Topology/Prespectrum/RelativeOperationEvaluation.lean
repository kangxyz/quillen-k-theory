/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.Topology.Prespectrum.RelativeLevelEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyComposition
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! Pointwise operation formulas with all prespectrum data abstract. -/
@[expose] public section
open CategoryTheory
open scoped unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F G : LoopPrespectrum.{u}} {f g : E ⟶ F} {H K L : Homotopy f g}

theorem level_trans_apply (J : H.RelHomotopy K) (J' : K.RelHomotopy L)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.trans J').level n (r, (s, x)) =
      if hr : (r : ℝ) ≤ 1 / 2 then
        J.level n (⟨2 * r, (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨r.2.1, hr⟩⟩, (s, x))
      else J'.level n (⟨2 * r - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 hr).le, r.2.2⟩⟩, (s, x)) :=
  ContinuousMap.HomotopyRel.trans_apply _ _ _

theorem level_symm_apply (J : H.RelHomotopy K) (n : ℕ)
    (r s : unitInterval) (x : E.space n) :
    J.symm.level n (r, (s, x)) = J.level n (unitInterval.symm r, (s, x)) := rfl

theorem level_eq_precomp_apply {f' g' : E ⟶ F} {H' K' : Homotopy f' g'}
    (J : H.RelHomotopy K) (J' : H'.RelHomotopy K') (a : G ⟶ E) (n : ℕ)
    (e : (J.level n).toContinuousMap = (J'.level n).toContinuousMap)
    (r s : unitInterval) (x : G.space n) :
    (precomp a J).level n (r, (s, x)) = (precomp a J').level n (r, (s, x)) :=
  level_eq_apply J J' n e r s (a.map n x)
/-- Project the right initial-track transport before specializing a native reversed pasting. -/
theorem level_symm_trans_replace {f' g' : E ⟶ F} {H' K' : Homotopy f' g'}
    (J : K.RelHomotopy H) (J' : K.RelHomotopy L) (J'' : H'.RelHomotopy K') (n : ℕ)
    (e : (J'.level n).toContinuousMap = (J''.level n).toContinuousMap)
    (r s : unitInterval) (x : E.space n) :
    (J.symm.trans J').level n (r, (s, x)) =
      if hr : (r : ℝ) ≤ 1 / 2 then
        J.level n (unitInterval.symm ⟨2 * r, (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨r.2.1, hr⟩⟩, (s, x))
      else J''.level n (⟨2 * r - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 hr).le, r.2.2⟩⟩, (s, x)) := by
  rw [level_trans_apply]
  split
  · exact level_symm_apply _ _ _ _ _
  · exact level_eq_apply _ _ n e _ s x

end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
