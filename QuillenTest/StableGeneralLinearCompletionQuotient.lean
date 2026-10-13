/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCompletionQuotient

/-! QuillenTest for the actual elementary kernel containment and quotient factorization. -/
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen
open Quillen.FiniteProjectiveModule.StableCompletion
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  Quillen.FiniteProjectiveModule.categoryDirectSumMonoidal
  Quillen.FiniteProjectiveModule.directSumMonoidal

example (R : Type u) [Ring R] :
    StableGeneralLinear.elementary R ≤ (stableGroupPiOneMap R).ker :=
  elementary_le_ker_stableGroupPiOneMap R

example (R : Type u) [Ring R] (g : StableGeneralLinear.Group R) :
    elementaryPiOneFactor R (StableGeneralLinear.quotientMap R g) = stableGroupPiOneMap R g := rfl

example (R : Type u) [Ring R]
    (f : StableGeneralLinear.ElementaryQuotient R →*
      HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R))
    (h : f.comp (StableGeneralLinear.quotientMap R) = stableGroupPiOneMap R) :
    f = elementaryPiOneFactor R := elementaryPiOneFactor_unique R f h

example : StableGeneralLinear.elementary (ZMod 1) ≤ (stableGroupPiOneMap (ZMod 1)).ker :=
  elementary_le_ker_stableGroupPiOneMap (ZMod 1)

example (R : Type u) [Ring R] :
    (StableGeneralLinear.elementary R).map
      (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)).toMonoidHom ≤
        (stablePiOneMap R).ker := elementaryPiOne_le_ker_stablePiOneMap R
