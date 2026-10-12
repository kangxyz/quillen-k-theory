/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.Topology.HomotopyFiber.LoopPrefixGroups
import Quillen.Topology.ClassifyingSpace.ProjectiveCompletionHomotopyFiber

/-! # Actual corrected loop maps and ring-category universe checks -/
noncomputable section
open scoped Topology
open Quillen Quillen.HomotopyFiber CategoryTheory
universe u v

example (R : Type u) [Ring R] :
    SmallCategory (FiniteProjectiveModule.GroupCompletionCategory R) := inferInstance

example (R : Type u) [Ring R] :
    SmallCategory (FiniteProjectiveModule.LocalizedExtensionCategory R) := inferInstance

example (R : Type u) [Ring R] :
    SmallCategory (FiniteProjectiveModule.exactStructure R).QCategory := inferInstance

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] (f : C(X, Y)) (x : X) (y : Y) (γ : Path (f x) y)
    (a : HomotopyGroup.Pi 0 (Path y y) (Path.refl y)) :
    pathTransport (loopPrefixUnitPath f x y γ) 0
      (homotopyGroupMap (loopPrefix f x y γ) rfl a) =
    pathTransport (loopEquivOfContractibleSourcePathUnitPath f x y γ) 0
      (homotopyGroupMap (loopEquivOfContractibleSourcePath f x y γ).toFun rfl a) :=
  loopPrefix_corrected_pi f x y γ 0 a
