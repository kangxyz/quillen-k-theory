/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.CategoryTheory.GroupCompletion.ProjectiveCoreCharacterMatrices

/-! Exact original matrix values and monoidal character consumers. -/
open CategoryTheory CategoryTheory.Limits MonoidalCategory Quillen Quillen.FiniteProjectiveModule
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  categoryDirectSumMonoidal directSumMonoidal
universe u
variable (R : Type u) [Ring R]

example (n : ℕ) (g : StableGeneralLinear.GL R n) :
    coreCharacter (rankOnePower Rᵐᵒᵖ n) (StableFree.powerEndEquiv R n g) =
      StableGeneralLinear.finiteClass R n g := coreCharacter_powerEndEquiv R n g

example (P Q : IsoCategory Rᵐᵒᵖ) (g : End P) (h : End Q) :
    coreCharacter (P ⊗ Q) (g ⊗ₘ h) = coreCharacter P g * coreCharacter Q h :=
  coreCharacter_tensor P Q g h

example (P Q : IsoCategory Rᵐᵒᵖ) (g : End Q) :
    coreCharacter (P ⊗ Q) (P ◁ g) = coreCharacter Q g :=
  coreCharacter_whiskerLeft P Q g
