/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.KTheory.Plus.ProjectiveCompletionComponents
public import Mathlib.Data.ZMod.Basic

/-! # Original completed-zero preimage consumers -/
open Quillen Quillen.FiniteProjectiveModule Quillen.FiniteProjectiveModule.StableFreeRight
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
universe u

example (R : Type u) [Ring R] :
    (classifyingSpaceMapUniversal (completionFunctor R)) ⁻¹'
      pathComponent (StableCompletion.zeroPoint R) =
    pathComponent (classifyingSpacePoint (projectiveTelescopeBase R)) :=
  completionMap_preimage_zeroComponent R

example :
    (classifyingSpaceMapUniversal (completionFunctor (ZMod 1))) ⁻¹'
      pathComponent (StableCompletion.zeroPoint (ZMod 1)) =
    pathComponent (classifyingSpacePoint (projectiveTelescopeBase (ZMod 1))) :=
  completionMap_preimage_zeroComponent (ZMod 1)
