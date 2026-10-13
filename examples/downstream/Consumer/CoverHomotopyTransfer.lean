/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.SimplyConnectedCover

/-! Independent consumption of actual total equivalences and original-realization covers. -/

@[expose] public section
noncomputable section
open Bundle CategoryTheory Quillen
open scoped Topology
universe u v
namespace Consumer.CoverHomotopyTransfer

variable {T X Y : Type u} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]

/-- The strict total-space inverse is accompanied by its actual inverse path. -/
def recoverPullbackPoint (p : C(T, Y)) (hp : IsCoveringMap p)
    (e : ContinuousMap.HomotopyEquiv X Y) (z : {z : X × T // p z.2 = e z.1}) :
    Path ((Covering.strictPullbackSourceHomotopyEquiv p hp e).invFun
      (Covering.strictPullbackSourceHomotopyEquiv p hp e z)) z :=
  (Covering.strictPullbackSourceHomotopyEquiv p hp e).left_inv.some.evalAt z

/-- The other genuine inverse homotopy returns every original covering point. -/
def recoverOriginalCoverPoint (p : C(T, Y)) (hp : IsCoveringMap p)
    (e : ContinuousMap.HomotopyEquiv X Y) (z : T) :
    Path (Covering.strictPullbackSourceHomotopyEquiv p hp e
      ((Covering.strictPullbackSourceHomotopyEquiv p hp e).invFun z)) z :=
  (Covering.strictPullbackSourceHomotopyEquiv p hp e).right_inv.some.evalAt z

/-- Independent object and morphism universes produce an actual cover of the original nerve. -/
theorem original_categorical_cover (C : Type u) [Category.{v} C]
    [PathConnectedSpace (ClassifyingSpace C)] (c : C) :
    ∃ T : Type (max u v), ∃ t : TopologicalSpace T,
      letI := t
      ∃ q : C(T, ClassifyingSpace C),
        IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace T :=
  RankedChainOrder.exists_simplyConnected_classifying_cover C c

end Consumer.CoverHomotopyTransfer
