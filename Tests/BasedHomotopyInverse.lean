/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.Topology.HomotopyFiber.ContractibleSourcePathGroups
/-! # Original transports, corrected inverses, and actual loop-fiber paths -/
open Quillen
noncomputable section
universe u v
example {X : Type u} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) (a : HomotopyGroup.Pi 0 X x) :
    pathTransport (p.trans q) 0 a = pathTransport q 0 (pathTransport p 0 a) :=
  pathTransport_trans p q 0 a
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) (y : Y) (p : Path (e x) y)
    (H : (e.invFun.comp e.toFun).Homotopy (ContinuousMap.id X))
    (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport ((p.symm.map e.invFun.continuous).trans (H.evalAt x)) n
      (homotopyGroupMap e.invFun rfl
        (pathTransport p n (homotopyGroupMap e.toFun rfl a))) = a :=
  pathTransport_homotopyEquiv_inverse e x y p H n a
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] (f : C(X, Y)) (x : X) (y : Y) (γ : Path (f x) y)
    (n : ℕ) (a : HomotopyGroup.Pi n (Path y y) (Path.refl y)) :
    pathTransport (HomotopyFiber.loopEquivOfContractibleSourcePathInverseBasepointPath f x y γ) n
      (homotopyGroupMap (HomotopyFiber.loopEquivOfContractibleSourcePath f x y γ).invFun rfl
        (pathTransport (HomotopyFiber.loopEquivOfContractibleSourcePathUnitPath f x y γ) n
          (homotopyGroupMap
            (HomotopyFiber.loopEquivOfContractibleSourcePath f x y γ).toFun rfl a))) = a :=
  HomotopyFiber.loopEquivOfContractibleSourcePath_inverse_pi f x y γ n a
