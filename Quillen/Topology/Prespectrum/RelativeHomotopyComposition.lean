/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.RelativeHomotopy

/-! Reverse and concatenate actual relative comparisons of whole prespectrum homotopies.
The comparison time remains independent of the original homotopy and structure times. -/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy

variable {E F : LoopPrespectrum.{u}} {f g : E ⟶ F} {H K L : Homotopy f g}

/-- Reverse only the comparison coordinate of an actual relative homotopy. -/
def symm (J : H.RelHomotopy K) : K.RelHomotopy H where
  level n := (J.level n).symm
  comm n r s x t := J.comm n (unitInterval.symm r) s x t

/-- Concatenate relative comparisons in their comparison coordinate, retaining the entire
original homotopy coordinate and its fixed boundary. -/
def trans (J : H.RelHomotopy K) (J' : K.RelHomotopy L) : H.RelHomotopy L where
  level n := (J.level n).trans (J'.level n)
  comm n r s x t := by
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split
    · exact J.comm _ _ _ _ _
    · exact J'.comm _ _ _ _ _

end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
