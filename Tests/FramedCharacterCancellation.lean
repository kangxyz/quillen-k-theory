/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.CategoryTheory.GroupCompletion.FramedCharacterCancellation
import Quillen.CategoryTheory.GroupCompletion.ProjectiveCoreCharacter

/-! Actual projective character cancellation, without cancellation of projective summands. -/
open CategoryTheory CategoryTheory.Limits MonoidalCategory Quillen
open Quillen.GroupCompletion.Localization Quillen.FiniteProjectiveModule
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
universe u
variable (R : Type u) [Ring R]

example {X : GroupCompletion.Localization (IsoCategory Rᵐᵒᵖ) (IsoCategory Rᵐᵒᵖ)}
    {Y Z : FramedPair (IsoCategory Rᵐᵒᵖ)} (r : X ⟶ Y.toLocalization) (f g : Y ⟶ Z)
    (h : r ≫ (framedInclusion (C := IsoCategory Rᵐᵒᵖ)).map f =
      r ≫ (framedInclusion (C := IsoCategory Rᵐᵒᵖ)).map g) :
    (framedCharacter coreCharacter (fun a b => coreCharacter_conjugate a b)
      coreCharacter_whiskerLeft).map f =
    (framedCharacter coreCharacter (fun a b => coreCharacter_conjugate a b)
      coreCharacter_whiskerLeft).map g :=
  framedCharacter_cancel _ _ _ r f g h
