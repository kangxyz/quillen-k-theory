/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.CategoryTheory.Monoidal.TranslationTelescopeCoherence
import Quillen.KTheory.Plus.ProjectiveTelescope

/-! Consumers for genuine telescope transformations and non-strict monoidal coherences. -/
universe u v
open CategoryTheory MonoidalCategory Quillen
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
example (e : C) : TranslationTelescope.leftTranslation e (𝟙_ C) ≅
    𝟭 (TranslationTelescope.Model e) := TranslationTelescope.leftTranslationUnit e
example (e P Q : C) : TranslationTelescope.leftTranslation e (P ⊗ Q) ≅
    TranslationTelescope.leftTranslation e Q ⋙ TranslationTelescope.leftTranslation e P :=
  TranslationTelescope.leftTranslationTensor e P Q
example (e : C) {P Q : C} (f : P ≅ Q) :
    TranslationTelescope.leftTranslation e P ≅ TranslationTelescope.leftTranslation e Q :=
  TranslationTelescope.leftTranslationIso e f

noncomputable section
open Quillen.FiniteProjectiveModule
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
example (R : Type u) [Ring R] (P Q : IsoCategory Rᵐᵒᵖ) :
    projectiveTelescopeTranslation R (P ⊗ Q) ≅
      projectiveTelescopeTranslation R Q ⋙ projectiveTelescopeTranslation R P :=
  TranslationTelescope.leftTranslationTensor _ _ _
