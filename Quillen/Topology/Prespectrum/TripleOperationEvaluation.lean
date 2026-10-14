/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.Topology.Prespectrum.RelativeOperationEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-! Literal level formulas for the remaining exported triple operations. -/
@[expose] public section
open CategoryTheory
open scoped unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F}

theorem level_hcomp_apply {H H' : Homotopy f g} {K K' : Homotopy g h}
    (J : H.RelHomotopy H') (L : K.RelHomotopy K') (n : ℕ) (r s : unitInterval)
    (x : E.space n) :
    (J.hcomp L).level n (r, (s, x)) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        J.level n (r, (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨s.2.1, hs⟩⟩, x))
      else L.level n (r, (⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

theorem level_cast_apply {f' g' : E ⟶ F} {H K : Homotopy f g}
    (J : H.RelHomotopy K) (hf : f = f') (hg : g = g')
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.cast hf hg).level n (r, (s, x)) = J.level n (r, (s, x)) := rfl
end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
