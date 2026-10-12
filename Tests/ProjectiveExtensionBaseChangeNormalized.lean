/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.KTheory.Plus.ProjectiveExtensionBaseChangeNormalized
import Mathlib.Data.ZMod.Basic

/-! # The exact original rebased Q functor and its extension square -/
noncomputable section
open CategoryTheory Quillen.FiniteProjectiveModule
universe u
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    (rightBaseChangeExact f).normalizedQ.obj (exactStructure Rᵐᵒᵖ).qZero =
      (exactStructure Sᵐᵒᵖ).qZero := rightBaseChangeNormalizedZero f

example {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (U : GroupCompletionCategory Rᵐᵒᵖ) :
    (localizedExtensionBaseChangeNormalizedIso f).hom.app
        ((completionIdentityEntry Rᵐᵒᵖ).obj U) ≫
      (localizedExtensionProjection Sᵐᵒᵖ).map
        ((completionIdentityBaseChangeNatIso f).hom.app U) ≫
      (completionIdentityProjectionIsoZero Sᵐᵒᵖ).hom.app ((completionBaseChange f).obj U) =
    (rightBaseChangeExact f).normalizedQ.map
        ((completionIdentityProjectionIsoZero Rᵐᵒᵖ).hom.app U) ≫
      eqToHom (rightBaseChangeNormalizedZero f) :=
  completionIdentityBaseChangeNormalized_triangle f U

example : (rightBaseChangeExact (Int.castRingHom (ZMod 1))).normalizedQ.obj
    (exactStructure ℤᵐᵒᵖ).qZero = (exactStructure (ZMod 1)ᵐᵒᵖ).qZero :=
  rightBaseChangeNormalizedZero (Int.castRingHom (ZMod 1))
