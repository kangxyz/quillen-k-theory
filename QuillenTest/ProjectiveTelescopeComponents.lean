/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.KTheory.Plus.ProjectiveTelescopeCorrection
import Mathlib.Algebra.Ring.PUnit
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Arbitrary-universe and noncommutative precompletion component tests -/

open CategoryTheory
open Quillen Quillen.FiniteProjectiveModule
universe u

example (R : Type u) [Ring R] (P : IsoCategory Rᵐᵒᵖ)
    (x y : ClassifyingSpace (ProjectiveTelescope R)) :
    Joined (classifyingSpaceMap (projectiveTelescopeTranslation R P) x)
      (classifyingSpaceMap (projectiveTelescopeTranslation R P) y) ↔ Joined x y :=
  projectiveTelescopeTranslation_joined_iff R P x y

example (P : IsoCategory (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ)
    (y : ClassifyingSpace (ProjectiveTelescope (Matrix (Fin 2) (Fin 2) ℤ))) :
    ∃ x, Joined (classifyingSpaceMap
      (projectiveTelescopeTranslation (Matrix (Fin 2) (Fin 2) ℤ) P) x) y :=
  projectiveTelescopeTranslation_surjective_components _ P y

example (P : IsoCategory PUnitᵐᵒᵖ)
    (x y : ClassifyingSpace (ProjectiveTelescope PUnit)) :
    Joined (classifyingSpaceMap (projectiveTelescopeTranslation PUnit P) x)
      (classifyingSpaceMap (projectiveTelescopeTranslation PUnit P) y) ↔ Joined x y :=
  projectiveTelescopeTranslation_joined_iff PUnit P x y

