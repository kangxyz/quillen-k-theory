/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus.StableGeneralLinearPlus
public import Mathlib.Data.ZMod.Basic

/-! # Actual ring-specific plus certification consumers, including the zero ring -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule.StableCompletion
universe u
namespace Quillen.Tests

/-- The original ring map satisfies the explicit homological plus specification. -/
example (R : Type u) [Ring R] :
    IsPlusConstruction.{u, u + 1, u + 1} (stableZeroMap R) (basepointPath R)
      (stableElementaryPiOneSubgroup R) :=
  stableZeroMap_isPlusConstruction R

/-- The original homology map is an isomorphism for every actual target system. -/
example (R : Type u) [Ring R]
    (A : LocalCoefficients.System.{u + 1, u + 1} (ZeroComponent R)) (n : ℕ) :
    IsIso (LocalCoefficients.UniverseLift.homologyMap (stableZeroMap R) A n) :=
  (stableZeroMap_isPlusConstruction R).homologyMap_isIso A n

/-- No nontrivial-ring or invariant-basis-number hypothesis is introduced by certification. -/
example : IsPlusConstruction.{0, 1, 1}
    (stableZeroMap (ZMod 1)) (basepointPath (ZMod 1))
    (stableElementaryPiOneSubgroup (ZMod 1)) :=
  stableZeroMap_isPlusConstruction (ZMod 1)

end Quillen.Tests
