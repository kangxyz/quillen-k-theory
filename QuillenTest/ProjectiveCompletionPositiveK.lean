/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.KTheory.Plus.ProjectiveCompletionPositiveK
public import Mathlib.Data.ZMod.Basic

/-! # Genuine positive K-group isomorphisms for the completion candidate -/
@[expose] public section
noncomputable section
universe u
open Quillen Quillen.FiniteProjectiveModule

example (R : Type u) [Ring R] (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (StableCompletion.ZeroComponent R)
      (StableCompletion.zeroBase R) ≃* (exactStructure Rᵐᵒᵖ).K (n + 1) :=
  StableCompletion.zeroCompletionPositiveKEquiv R n

example : HomotopyGroup.Pi 1 (StableCompletion.ZeroComponent (ZMod 1))
    (StableCompletion.zeroBase (ZMod 1)) ≃* (exactStructure (ZMod 1)ᵐᵒᵖ).K 1 :=
  StableCompletion.zeroCompletionPositiveKEquiv (ZMod 1) 0

example (R : Type u) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (StableCompletion.ZeroComponent R)
      (StableCompletion.zeroBase R)) :
    StableCompletion.zeroCompletionPositiveKEquiv R n a =
      completionPositiveKEquiv Rᵐᵒᵖ (StableCompletion.stageObject R 0) n
        (homotopyGroupMapHom (N := Fin (n + 1))
          (pathComponentInclusion (StableCompletion.zeroPoint R))
          (x := StableCompletion.zeroBase R) rfl a) :=
  StableCompletion.zeroCompletionPositiveKEquiv_apply R n a
