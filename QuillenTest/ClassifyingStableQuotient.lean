/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.Topology.ClassifyingSpace.StableElementaryQuotient

/-! Test the stable quotient on realized edge loops and its full fundamental-group kernel. -/

open Quillen.StableGeneralLinear
open Quillen.GroupoidClassifying

universe u
variable {R S : Type u} [Ring R] [Ring S]

example : Function.Surjective (quotientPiOneMap R) := quotientPiOneMap_surjective R

example :
    (piOneMap (quotientMap R)).ker = (elementary R).map
      (singleObjPiOneEquiv (Quillen.StableGeneralLinear.Group R)).toMonoidHom :=
  ker_quotientPiOneMap R

example (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : R) :
    quotientPiOneMap R
      (singleObjPiOneEquiv (Quillen.StableGeneralLinear.Group R)
        (of R n (Quillen.ElementaryMatrix.unit i j hij a))) = 1 :=
  (quotientPiOneMap_equiv_eq_one_iff R _).mpr (unit_mem_elementary R n i j hij a)

example (f : R →+* S) :
    (quotientPiOneMap S).comp (piOneMap (Quillen.StableGeneralLinear.map f)) =
      (piOneMap (quotientRingMap f)).comp (quotientPiOneMap R) :=
  quotientPiOneMap_naturality f
