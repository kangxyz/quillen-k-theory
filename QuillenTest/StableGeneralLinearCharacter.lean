/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.CategoryTheory.GroupCompletion.StableGeneralLinearCharacter

/-! Original quotient-projection compatibility on the actual stable telescope. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen Quillen.FiniteProjectiveModule
open Quillen.FiniteProjectiveModule.StableCompletion
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
universe u
variable (R : Type u) [Ring R]

example : telescopeFunctor R ⋙ stableCompletionCharacter R ≅
    StableGeneralLinear.GrothendieckModel.projection R ⋙ quotientCategoryFunctor R :=
  telescopeCharacterIso R

example : telescopeFramedFunctor R ⋙ stableFramedCharacter R =
    StableGeneralLinear.GrothendieckModel.projection R ⋙ quotientCategoryFunctor R :=
  telescopeFramed_character R
