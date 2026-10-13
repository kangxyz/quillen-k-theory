/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCompletionBasedSurjectivity

/-! Consumer checks for original finite-matrix representatives and realized surjectivity. -/

attribute [local instance] CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts
  Quillen.FiniteProjectiveModule.categoryDirectSumMonoidal
  Quillen.FiniteProjectiveModule.directSumMonoidal
  Quillen.FiniteProjectiveModule.directSumSymmetric

open CategoryTheory Quillen Quillen.FiniteProjectiveModule.StableCompletion

universe u
variable (R : Type u) [Ring R]

example : Function.Surjective (stablePiOneMap R) := stablePiOneMap_surjective R

example : Function.Surjective (stableGroupPiOneMap R) := stableGroupPiOneMap_surjective R

example : Function.Surjective (elementaryPiOneFactor R) := elementaryPiOneFactor_surjective R

example : Function.Surjective (elementaryPiOneFactor (Matrix (Fin 2) (Fin 2) ℤ)) :=
  elementaryPiOneFactor_surjective _

example : Function.Surjective (elementaryPiOneFactor (ZMod 1)) :=
  elementaryPiOneFactor_surjective _

example (t : unitInterval) :
    telescopeZeroMap R (sourceBasepointPath R t) = basepointPath R t :=
  sourceBasepointPath_map R t
