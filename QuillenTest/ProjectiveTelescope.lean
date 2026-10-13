/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.KTheory.Plus.ProjectiveTelescope
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic

/-! The precompletion telescope accepts arbitrary right-module coefficient rings. -/
universe u
noncomputable section
open CategoryTheory Quillen.FiniteProjectiveModule

example (R : Type u) [Ring R] : ℕ ⥤ Cat.{u + 1, u + 1} :=
  projectiveTelescopeDiagram R
example (R : Type u) [Ring R] (P : IsoCategory Rᵐᵒᵖ) :
    ProjectiveTelescope R ⥤ ProjectiveTelescope R := projectiveTelescopeTranslation R P
example : ProjectiveTelescope (ZMod 1) := projectiveTelescopeBase _
example : ProjectiveTelescope (Matrix (Fin 2) (Fin 2) ℤ) := projectiveTelescopeBase _
example (R : Type u) [Ring R] (P : IsoCategory Rᵐᵒᵖ) :
    (projectiveTelescopeTranslation R P).obj (projectiveTelescopeBase R) ≅
      (⟨0, AsSmall.up.obj P⟩ : ProjectiveTelescope R) :=
  projectiveTelescopeTranslationBaseIso R P
