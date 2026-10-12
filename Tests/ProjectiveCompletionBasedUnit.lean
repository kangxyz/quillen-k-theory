/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.KTheory.Plus.ProjectiveCompletionBasedUnit
public import Mathlib.Data.ZMod.Basic

/-! # Exact original-basepoint comparison-track consumers -/
open Quillen Quillen.FiniteProjectiveModule Quillen.FiniteProjectiveModule.StableFreeRight
universe u

example (R : Type u) [Ring R] :
    telescopeUnitCompletionBasePathAligned R = completedRetractionZeroPath R :=
  telescopeUnitCompletionBasePathAligned_eq R

example (R : Type u) [Ring R] (t : unitInterval) :
    telescopeUnitCompletionHomotopy R (t, classifyingSpacePoint (projectiveTelescopeBase R)) =
      completedRetractionZeroPath R t := telescopeUnitCompletionHomotopy_base R t

example : telescopeUnitCompletionBasePathAligned (ZMod 1) =
    completedRetractionZeroPath (ZMod 1) := telescopeUnitCompletionBasePathAligned_eq (ZMod 1)
