/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.KTheory.Plus.ProjectiveCompletionAllComponents
public import Mathlib.Data.ZMod.Basic

/-! # Original telescope completion map on every actual path component -/
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
open Quillen.FiniteProjectiveModule.StableFreeRight
universe u
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric

example (R : Type u) [Ring R] :
    ZerothHomotopy (ClassifyingSpace (ProjectiveTelescope R)) ≃
      ZerothHomotopy (ClassifyingSpace (StableCompletion.Completion R)) :=
  completionMapComponentsEquiv R

example (R : Type u) [Ring R] (x : ClassifyingSpace (ProjectiveTelescope R)) :
    completionMapComponentsEquiv R (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (classifyingSpaceMapUniversal (completionFunctor R) x) := rfl

example (R : Type u) [Ring R] (x y : ClassifyingSpace (ProjectiveTelescope R)) :
    Joined (classifyingSpaceMapUniversal (completionFunctor R) x)
      (classifyingSpaceMapUniversal (completionFunctor R) y) ↔ Joined x y :=
  completionMap_joined_iff R x y

example :
    ZerothHomotopy (ClassifyingSpace (ProjectiveTelescope (ZMod 1))) ≃
      ZerothHomotopy (ClassifyingSpace (StableCompletion.Completion (ZMod 1))) :=
  completionMapComponentsEquiv (ZMod 1)
