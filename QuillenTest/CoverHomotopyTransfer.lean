/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Covering.FiberBundlePullback

/-! Named tests for the literal pullback topology and exact projection maps. -/

@[expose] public section
noncomputable section
open Bundle Quillen
open scoped Topology
universe u
namespace QuillenTest.CoverHomotopyTransfer

variable {T X Y : Type u} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]

/-- The strict total-space equivalence keeps the exact old covering point. -/
theorem old_total_projection (p : C(T, Y)) (hp : IsCoveringMap p)
    (e : ContinuousMap.HomotopyEquiv X Y) (z : {z : X × T // p z.2 = e z.1}) :
    Covering.strictPullbackSourceHomotopyEquiv p hp e z = z.1.2 := rfl

/-- The strict pullback square is an equality of original base points. -/
theorem strict_projection_square (p : C(T, Y)) (hp : IsCoveringMap p)
    (e : ContinuousMap.HomotopyEquiv X Y) (z : {z : X × T // p z.2 = e z.1}) :
    p (Covering.strictPullbackSourceHomotopyEquiv p hp e z) = e z.1.1 := z.2

variable (F : Type u) (E : Y → Type u) [TopologicalSpace (TotalSpace F E)]

/-- The actual bundle pullback topology is retained by an inducing homeomorphism. -/
theorem literal_pullback_topology (f : C(X, Y)) :
    Topology.IsInducing (Covering.pullbackStrictHomeomorph F E f) :=
  (Covering.pullbackStrictHomeomorph F E f).isInducing

/-- The homeomorphism retains the new base and old total point simultaneously. -/
theorem literal_bundle_coordinates (f : C(X, Y))
    (z : TotalSpace F ((f : X → Y) *ᵖ E)) :
    (Covering.pullbackStrictHomeomorph F E f z).val = (z.proj, Pullback.lift f z) := rfl

end QuillenTest.CoverHomotopyTransfer
