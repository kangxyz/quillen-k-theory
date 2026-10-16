/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackSpatial

/-! Literal independent coordinates in original normalized cube self-tracks. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open Quillen
universe u
namespace QuillenTest.GenLoopSelfTrackSpatial

/-- Spatial concatenation keeps the actual self-track parameter independent. -/
theorem original_spatial_track_time {X : Type u} [TopologicalSpace X] {x : X}
    (m : ℕ) {p q : GenLoop (Fin (m + 2)) X x} (α : Path p p) (β : Path q q)
    (t : unitInterval) (z : Fin (m + 2) → unitInterval) :
    genLoopTransAtPath (1 : Fin (m + 2)) α β t z =
      GenLoop.transAt (1 : Fin (m + 2)) (α t) (β t) z := rfl

end QuillenTest.GenLoopSelfTrackSpatial
