/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.KTheory.Plus.ProjectiveTelescopeAbelianHomology
import Mathlib.Algebra.Ring.PUnit

/-! # Actual abelian local homology isomorphisms, including the zero ring -/

open CategoryTheory Quillen Quillen.FiniteProjectiveModule Quillen.LocalCoefficients
universe u

example (R : Type u) [Ring R] (P : IsoCategory Rᵐᵒᵖ)
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescope R)))
    (hA : AbelianMonodromy A) (k : ℕ) :
    IsIso (pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom A k) :=
  projectiveTelescopeTranslation_abelianHomology_isIso R P A hA k

example (P : IsoCategory PUnitᵐᵒᵖ)
    (A : System.{1, 1} (ClassifyingSpace (ProjectiveTelescope PUnit)))
    (hA : AbelianMonodromy A) (k : ℕ) :
    IsIso (pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation PUnit P)).hom A k) :=
  projectiveTelescopeTranslation_abelianHomology_isIso PUnit P A hA k
