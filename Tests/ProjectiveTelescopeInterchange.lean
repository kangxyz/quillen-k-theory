/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
import Quillen.KTheory.Plus.ProjectiveTelescopeInterchange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-! # Actual localization–telescope interchange and original unit tests -/

open CategoryTheory MonoidalCategory Quillen Quillen.FiniteProjectiveModule
open Quillen.GroupCompletion
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal projectiveTelescopeAction
universe u v
attribute [local instance] TranslationTelescope.monoidalLeftAction
noncomputable section

example {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C) :
    (TranslationTelescope.localizationInterchange e).IsEquivalence := inferInstance

example (R : Type u) [Ring R] (n : ℕ) :
    Grothendieck.ι (projectiveCompletedTelescopeDiagram R) n ⋙
        (projectiveTelescopeInterchange R).functor = projectiveCompletionStage R n :=
  projectiveTelescopeInterchange_stage R n

example (R : Type u) [Ring R] (n : ℕ) :
    Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := IsoCategory Rᵐᵒᵖ) ⋙
        projectiveCompletionStage R n =
      TranslationTelescope.stageInclusion (freeIso Rᵐᵒᵖ 1) n ⋙
        Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := ProjectiveTelescope R) :=
  projectiveCompletionStage_unit R n

example :
    Grothendieck (projectiveCompletedTelescopeDiagram (Matrix (Fin 2) (Fin 2) ℤ)) ≌
      ProjectiveTelescopeLocalization (Matrix (Fin 2) (Fin 2) ℤ) :=
  projectiveTelescopeInterchange _

example : Grothendieck (projectiveCompletedTelescopeDiagram (ZMod 1)) ≌
    ProjectiveTelescopeLocalization (ZMod 1) := projectiveTelescopeInterchange _

example (R : Type u) [Ring R] :
    (projectiveTelescopeInterchangeHomotopyEquiv R).toFun =
      classifyingSpaceMapUniversal (projectiveTelescopeInterchange R).functor :=
  projectiveTelescopeInterchangeHomotopyEquiv_toFun R
