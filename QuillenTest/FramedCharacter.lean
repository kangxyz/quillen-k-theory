/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.CategoryTheory.GroupCompletion.FramedCharacter
import Quillen.CategoryTheory.GroupCompletion.ProjectiveCoreCharacter

/-! Actual original-arrow and matrix-character consumers. -/
open CategoryTheory CategoryTheory.Limits MonoidalCategory Quillen
open Quillen.GroupCompletion.Localization Quillen.FiniteProjectiveModule
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  categoryDirectSumMonoidal directSumMonoidal
noncomputable section
universe u
variable (R : Type u) [Ring R]

example : FramedPair (IsoCategory Rᵐᵒᵖ) ⥤ SingleObj (StableGeneralLinear.ElementaryQuotient R) :=
  framedCharacter coreCharacter (fun f g => coreCharacter_conjugate f g) coreCharacter_whiskerLeft

example (P : IsoCategory Rᵐᵒᵖ) (g : End P) :
    (framedCharacter coreCharacter (fun f g => coreCharacter_conjugate f g)
      coreCharacter_whiskerLeft).map
      (show diagonalFrame P ⟶ diagonalFrame P from
        GroupCompletion.ActionLocalization.ofHom (𝟙 P, g)) = coreCharacter P g :=
  framedCharacter_numerator _ _ _ P g
