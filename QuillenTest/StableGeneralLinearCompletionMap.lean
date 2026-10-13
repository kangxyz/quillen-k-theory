/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.CategoryTheory.GroupCompletion.StableGeneralLinearMap

/-! QuillenTest for the original matrix action and actual projective localization functor. -/
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.StableGeneralLinear
open Quillen.FiniteProjectiveModule.StableCompletion
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  Quillen.FiniteProjectiveModule.categoryDirectSumMonoidal
  Quillen.FiniteProjectiveModule.directSumMonoidal

example (R : Type u) [Ring R] (n : ℕ) (g : GL R n) :
    stageAction R n g ≫ stageArrow R n = stageArrow R n ≫ stageAction R (n + 1) (step R n g) :=
  stageAction_step R n g

example (R : Type u) [Ring R] (n : ℕ) :
    CategoryTheory.Grothendieck.ι (categoryDiagram R) (rankIndex n) ⋙ telescopeFunctor R =
      stageFunctor R n := inclusion_telescopeFunctor R n

example : GrothendieckModel.Telescope (ZMod 1) ⥤ Completion (ZMod 1) :=
  telescopeFunctor (ZMod 1)

example (R : Type u) [Ring R] :
    GrothendieckModel.Telescope (Matrix (Fin 2) (Fin 2) R) ⥤
      Completion (Matrix (Fin 2) (Fin 2) R) := telescopeFunctor _
