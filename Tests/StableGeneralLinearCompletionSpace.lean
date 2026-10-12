/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCompletion

/-! Tests for the actual stable matrix map to the zero component of projective completion. -/
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen
open Quillen.FiniteProjectiveModule.StableCompletion
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  Quillen.FiniteProjectiveModule.categoryDirectSumMonoidal
  Quillen.FiniteProjectiveModule.directSumMonoidal

example (R : Type u) [Ring R] :
    C(ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)), ZeroComponent R) :=
  stableZeroMap R

example (R : Type u) [Ring R] (x : ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))) :
    (stableZeroMap R x).val = stableMap R x := rfl

example (R : Type u) [Ring R] (n : ℕ) :
    ((smallStableMap R).comp (classifyingSpaceMap
      (StableGeneralLinear.smallFunctor (StableGeneralLinear.of R n))).hom).Homotopic
        (classifyingSpaceMapUniversal (stageFunctor R n)) := smallStableMap_stage R n

example : C(ClassifyingSpace (SingleObj (StableGeneralLinear.Group (ZMod 1))),
    ZeroComponent (ZMod 1)) := stableZeroMap _

example (R : Type u) [Ring R] :
    C(ClassifyingSpace (SingleObj (StableGeneralLinear.Group (Matrix (Fin 2) (Fin 2) R))),
      ZeroComponent (Matrix (Fin 2) (Fin 2) R)) := stableZeroMap _
