/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.KTheory.Plus.ProjectiveCompletionUnitHomotopy
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic

/-! # Original unit-preserving completed-model comparison consumers -/
noncomputable section
open CategoryTheory MonoidalCategory
open Quillen Quillen.FiniteProjectiveModule Quillen.FiniteProjectiveModule.StableFreeRight
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
universe u

example (R : Type u) [Ring R] :
    TranslationTelescope.telescopeUnit (freeIso Rᵐᵒᵖ 1) ⋙ completedRetraction R ⟶
      completionFunctor R := telescopeUnitCompletionHom R

example (R : Type u) [Ring R] :
    ((classifyingSpaceMapUniversal (completedRetraction R)).comp
      (classifyingSpaceMapUniversal
        (TranslationTelescope.telescopeUnit (freeIso Rᵐᵒᵖ 1)))).Homotopy
      (classifyingSpaceMapUniversal (completionFunctor R)) := telescopeUnitCompletionHomotopy R

example (R : Type u) [Ring R] :
    (TranslationTelescope.telescopeUnit (freeIso Rᵐᵒᵖ 1)).obj
      (projectiveTelescopeBase R) = completedTelescopeBase R := telescopeUnit_base R

example :
    TranslationTelescope.telescopeUnit (freeIso (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ 1) ⋙
      completedRetraction (Matrix (Fin 2) (Fin 2) ℤ) ⟶
      completionFunctor (Matrix (Fin 2) (Fin 2) ℤ) :=
  telescopeUnitCompletionHom (Matrix (Fin 2) (Fin 2) ℤ)

example :
    (TranslationTelescope.telescopeUnit (freeIso (ZMod 1)ᵐᵒᵖ 1)).obj
      (projectiveTelescopeBase (ZMod 1)) = completedTelescopeBase (ZMod 1) :=
  telescopeUnit_base (ZMod 1)
