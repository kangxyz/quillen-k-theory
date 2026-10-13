/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.HomotopyFiber.LoopPrefixNaturality

/-! # Exact contraction-free loop-prefix consumers -/
noncomputable section
open scoped Topology
open Quillen.HomotopyFiber
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

example (f : C(X, Y)) (x : X) (y : Y) (γ : Path (f x) y) (δ : Path y y) :
    (loopPrefix f x y γ δ).val.2 = (γ.trans δ).toContinuousMap := rfl

example [ContractibleSpace X] (f : C(X, Y)) (x : X) (y : Y) (γ : Path (f x) y) :
    loopPrefix f x y γ = (loopEquivOfContractibleSourcePath f x y γ).toFun :=
  loopPrefix_eq_forward f x y γ

example [ContractibleSpace X] (f : C(X, Y)) (x : X) (y : Y)
    (γ : Path (f x) y) (t : unitInterval) :
    loopPrefixUnitPath f x y γ t =
      loopEquivOfContractibleSourcePathUnitPath f x y γ t := rfl
