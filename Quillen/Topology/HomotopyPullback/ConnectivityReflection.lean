/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.HomotopyPullback.Connectivity
public import Quillen.Topology.HomotopyFiber.BasepointTransport

/-!
# Reflecting finite connectivity from the original pullback projection

Over a path-connected target and one actual parameter point, the genuine fiber equivalence
and displayed target paths transfer all finite fiber bounds back to the unchanged map.
Nonempty actual fibers and every original fiber basepoint are included.
-/
@[expose] public section
noncomputable section
universe u
namespace Quillen.HomotopyPullback
variable {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]

/-- The original map inherits a finite bound from its actual pullback projection, using the
supplied parameter point and actual target paths rather than a chosen inverse map. -/
theorem isHomotopyConnectedMap_of_baseProjection (f : C(X, B)) (g : C(A, B))
    [PathConnectedSpace B] (a : A) (n : ℕ)
    (h : IsHomotopyConnectedMap (baseProjection f g) n) :
    IsHomotopyConnectedMap f n := by
  let e := baseFiberHomotopyEquiv f g a
  have hn : Nonempty (HomotopyFiber f (g a)) := (h.fiber_nonempty a).map e.invFun
  have hs (z : HomotopyFiber f (g a)) (k : ℕ) (hk : k < n) :
      Subsingleton (HomotopyGroup.Pi k (HomotopyFiber f (g a)) z) := by
    let := h.fiber_subsingleton a (e z) k hk
    exact (homotopyGroupMap_bijective_of_homotopyEquiv e rfl k).injective.subsingleton
  refine ⟨?_, ?_⟩
  · intro y
    exact hn.map (HomotopyFiber.basepointTransportEquiv f
      (PathConnectedSpace.joined (g a) y).somePath)
  · intro y z k hk
    let t := HomotopyFiber.basepointTransportEquiv f
      (PathConnectedSpace.joined y (g a)).somePath
    let := hs (t z) k hk
    exact (homotopyGroupMap_bijective_of_homotopyEquiv t rfl k).injective.subsingleton

end Quillen.HomotopyPullback
