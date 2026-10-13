/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.Topology.ClassifyingSpace.StableGeneralLinearCompletionStages

/-! Test compatibility with the original finite general linear group inclusions. -/
universe u
open CategoryTheory CategoryTheory.Limits Quillen
open Quillen.FiniteProjectiveModule.StableCompletion
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  Quillen.FiniteProjectiveModule.categoryDirectSumMonoidal
  Quillen.FiniteProjectiveModule.directSumMonoidal

example (R : Type u) [Ring R] (n : ℕ) :
    ((stableMap R).comp (StableGeneralLinear.stageMap R n).hom).Homotopic
      (finiteCompletionMap R n) := stableMap_stage R n
