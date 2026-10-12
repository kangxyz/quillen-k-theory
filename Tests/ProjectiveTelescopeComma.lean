/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
import Quillen.KTheory.Plus.ProjectiveTelescopeComma

/-! # Original action, actual comma transports, and the specified unit entry -/

open CategoryTheory MonoidalCategory Quillen Quillen.FiniteProjectiveModule
open Quillen.LocalCoefficients Quillen.GroupCompletion
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  projectiveTelescopeAction
universe u v
noncomputable section

example {C : Type u} [Category.{v} C] [MonoidalCategory C] (e P : C) :
    letI := TranslationTelescope.monoidalLeftAction e
    MonoidalLeftAction.actionLeft (TranslationTelescope.Model e) P =
      TranslationTelescope.leftTranslation e P :=
  TranslationTelescope.actionLeft_eq_leftTranslation e P

example (R : Type u) [Ring R]
    {X Y : ActionLocalization (IsoCategory Rᵐᵒᵖ) (IsoCategory Rᵐᵒᵖ)} (f : X ⟶ Y)
    (A : System.{u + 1, u + 1}
      (ClassifyingSpace (CostructuredArrow (projectiveTelescopeProjection R) Y)))
    (hA : AbelianMonodromy A) (n : ℕ) :
    IsIso (pushforwardHomologyMap (classifyingSpaceMapUniversal
      (CostructuredArrow.map (S := projectiveTelescopeProjection R) f)) A n) :=
  projectiveTelescopeProjection_comma_abelianHomology_isIso R f A hA n

example (R : Type u) [Ring R] :
    projectiveTelescopeReplacementEntry R ≫
      TheoremA.diagonalSourceMap (projectiveTelescopeProjection R) =
      nerveMap (Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := ProjectiveTelescope R)) :=
  projectiveTelescopeReplacementEntry_source R
