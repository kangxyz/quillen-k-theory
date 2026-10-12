/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCompletionKernel

/-! The original stable completion map has exactly its elementary kernel. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.FiniteProjectiveModule
open Quillen.FiniteProjectiveModule.StableCompletion
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
universe u
variable (R : Type u) [Ring R]

example : (stableGroupPiOneMap R).ker = StableGeneralLinear.elementary R :=
  ker_stableGroupPiOneMap R

example : (stablePiOneMap R).ker = (StableGeneralLinear.elementary R).map
    (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)).toMonoidHom :=
  ker_stablePiOneMap R

example : StableGeneralLinear.ElementaryQuotient R ≃*
    HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R) := elementaryPiOneEquiv R

example (g : StableGeneralLinear.Group R) :
    elementaryPiOneEquiv R (StableGeneralLinear.quotientMap R g) = stableGroupPiOneMap R g :=
  elementaryPiOneEquiv_quotientMap R g

example : (stableGroupPiOneMap (Matrix (Fin 2) (Fin 2) ℤ)).ker =
    StableGeneralLinear.elementary (Matrix (Fin 2) (Fin 2) ℤ) := ker_stableGroupPiOneMap _

example : (stableGroupPiOneMap (ZMod 1)).ker = StableGeneralLinear.elementary (ZMod 1) :=
  ker_stableGroupPiOneMap _

example (a : HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R)) :
    (elementaryPiOneEquiv R).symm a = zeroPiOneDetector R a := elementaryPiOneEquiv_symm R a
