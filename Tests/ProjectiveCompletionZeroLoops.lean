/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.KTheory.Plus.ProjectiveCompletionZeroLoops
public import Mathlib.Data.ZMod.Basic

/-! # Original zero-component loop comparison consumers -/
open Quillen Quillen.FiniteProjectiveModule Quillen.FiniteProjectiveModule.StableCompletion
universe u v

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : IsWeakHomotopyEquivalence f) (x : X) (y : Y)
    (p : Path (f x) y) : IsWeakHomotopyEquivalence (pathComponentMap f x y ⟨p⟩) :=
  hf.pathComponentMap x y ⟨p⟩

example (R : Type u) [Ring R] :
    IsWeakHomotopyEquivalence (zeroCompletionToOriginalQLoops R) :=
  zeroCompletionToOriginalQLoops_isWeakHomotopyEquivalence R

example (R : Type u) [Ring R] (x : ZeroComponent R) :
    (zeroCompletionToOriginalQLoops R x).val =
      completionToOriginalQLoops Rᵐᵒᵖ (stageObject R 0) x.val := rfl

example (R : Type u) [Ring R] (t : unitInterval) :
    (zeroCompletionToOriginalQLoopsBasepointPath R t).val =
      completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (stageObject R 0) t := rfl

example : IsWeakHomotopyEquivalence (zeroCompletionToOriginalQLoops (ZMod 1)) :=
  zeroCompletionToOriginalQLoops_isWeakHomotopyEquivalence (ZMod 1)
