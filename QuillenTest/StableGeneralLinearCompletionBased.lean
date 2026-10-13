/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCompletionBased

/-! QuillenTest for the actual inverse-homotopy basepoint correction and fundamental-group map. -/
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen
open Quillen.FiniteProjectiveModule.StableCompletion
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  Quillen.FiniteProjectiveModule.categoryDirectSumMonoidal
  Quillen.FiniteProjectiveModule.directSumMonoidal

example (R : Type u) [Ring R] :
    Path (stableZeroMap R (stableBase R)) (zeroBase R) := basepointPath R

example (R : Type u) [Ring R] (t : unitInterval) :
    basepointPath R t = finiteZeroHomotopy R 0
      (t, classifyingSpacePoint (AsSmall.up.obj (SingleObj.star (StableGeneralLinear.GL R 0)))) :=
  basepointPath_eq_finiteZeroHomotopy R t

example (R : Type u) [Ring R] : StableGeneralLinear.Group R →*
    HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R) := stableGroupPiOneMap R

example : StableGeneralLinear.Group (ZMod 1) →*
    HomotopyGroup.Pi 1 (ZeroComponent (ZMod 1)) (zeroBase (ZMod 1)) := stableGroupPiOneMap _
