/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.Topology.HomotopyFiber.LoopPrefixBasepointNaturality

/-! # Actual fiber-basepoint paths in the original loop comparison -/

noncomputable section

open scoped Topology unitInterval
open Quillen Quillen.HomotopyFiber

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

-- The arbitrary-fiber API specializes to the displayed original points and paths.
example [ContractibleSpace X] (f : C(X, Y)) (y : Y) (x₀ x₁ : X)
    (γ₀ : Path (f x₀) y) (γ₁ : Path (f x₁) y)
    (q : Path (pointWithPath f x₀ y γ₀) (pointWithPath f x₁ y γ₁)) (n : ℕ)
    (b : HomotopyGroup.Pi n (HomotopyFiber f y) (pointWithPath f x₀ y γ₀)) :
    pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath f x₀ y γ₀) n
      (homotopyGroupMap (loopEquivOfContractibleSourcePath f x₀ y γ₀).invFun rfl b) =
    pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath f x₁ y γ₁) n
      (homotopyGroupMap (loopEquivOfContractibleSourcePath f x₁ y γ₁).invFun rfl
        (pathTransport q n b)) :=
  loopInverse_pathTransport_pi q n b

-- No contractibility is needed to retain the entire original unit-removal square.
example (f : C(X, Y)) (y : Y) {z w : HomotopyFiber f y} (q : Path z w)
    (t s : unitInterval) :
    (loopPrefixUnitSquare q (t, s)).val.2 =
      (Path.delayReflRight t (toPath f y (q s))).toContinuousMap := rfl

-- Cancellation detects the actual trivial path action, including degree zero.
example [ContractibleSpace X] (f : C(X, Y)) (y : Y) (z : HomotopyFiber f y)
    (q : Path z z) (n : ℕ) (b : HomotopyGroup.Pi n (HomotopyFiber f y) z) :
    pathTransport q n b = b := by
  have h := loopInverse_pathTransport_pi q n b
  have hf := congrArg (fun a ↦
    pathTransport (loopEquivOfContractibleSourcePathUnitPath f z.val.1 y (toPath f y z)) n
      (homotopyGroupMap (loopEquivOfContractibleSourcePath f z.val.1 y
        (toPath f y z)).toFun rfl a)) h
  rw [loopEquivOfContractibleSourcePath_forward_pi f z.val.1 y (toPath f y z) n b,
    loopEquivOfContractibleSourcePath_forward_pi f z.val.1 y (toPath f y z) n
      (pathTransport q n b)] at hf
  exact hf.symm
