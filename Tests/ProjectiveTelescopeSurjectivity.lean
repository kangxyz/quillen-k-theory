/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
import Quillen.KTheory.Plus.ProjectiveTelescopeSurjectivity
import Mathlib.Algebra.Ring.PUnit

/-! # Actual all-target local homology surjectivity, including the zero ring -/

open CategoryTheory Quillen Quillen.FiniteProjectiveModule Quillen.LocalCoefficients
universe u

example (R : Type u) [Ring R] (P : IsoCategory Rᵐᵒᵖ)
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescope R))) (k : ℕ) :
    Epi (pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom A k) :=
  projectiveTelescopeTranslation_homology_epi R P A k

example (P : IsoCategory PUnitᵐᵒᵖ)
    (A : System.{1, 1} (ClassifyingSpace (ProjectiveTelescope PUnit))) (k : ℕ) :
    Function.Surjective (pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation PUnit P)).hom A k) :=
  projectiveTelescopeTranslation_homology_surjective PUnit P A k
