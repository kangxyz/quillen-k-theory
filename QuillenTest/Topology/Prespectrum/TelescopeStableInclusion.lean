/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.TelescopeStableInclusion

/-!
# Canonical stable-leg consumers

These clients recover bijectivity of the actual stage-zero inclusion including
K-zero, and the actual stage-`i` inclusion in degree `-i`, from the expected
transition stability range. The latter needs no invertibility before `i`.
-/
@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true

open CategoryTheory
open Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.TelescopeStableInclusion
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  [∀ i k, T1Space ((E i).space k)]
  (h : ∀ (i : ℕ) (d : ℤ), -(i : ℤ) ≤ d →
    IsIso ((stableHomotopyFunctor d).map (f i)))

include h

/-- The original stage-zero comparison is bijective in every nonnegative degree. -/
theorem stage_zero_bijective (d : ℤ) (hd : 0 ≤ d) :
    Function.Bijective ((stableHomotopyFunctor d).map (Telescope.inclusion E f 0)) := by
  have := Telescope.inclusion_stableMap_isIso_of_tail E f d 0 (by
    intro n _
    exact h n d (by omega))
  exact ConcreteCategory.bijective_of_isIso _

/-- The boundary degree uses stage `i` itself, including `i = 0`. -/
theorem original_negative_stage_bijective (i : ℕ) :
    Function.Bijective
      ((stableHomotopyFunctor (-(i : ℤ))).map (Telescope.inclusion E f i)) := by
  have := Telescope.inclusion_stableMap_isIso_of_tail E f (-(i : ℤ)) i (by
    intro n hn
    exact h n (-(i : ℤ)) (by omega))
  exact ConcreteCategory.bijective_of_isIso _

end QuillenTest.TelescopeStableInclusion
