/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackSpatialProduct

/-! The original second spatial direction becomes the third output coordinate. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open Quillen
universe u
namespace QuillenTest.GenLoopSelfTrackSpatialProduct

/-- At input dimension at least two, the actual normalized cubes retain spatial concatenation. -/
theorem original_spare_coordinate_product {X : Type u} [TopologicalSpace X] {x : X}
    (m : ℕ) (p q : GenLoop (Fin (m + 2)) X x) (α : Path p p) (β : Path q q) :
    genLoopNormalizedSelfTrackCube (m + 1) (GenLoop.transAt 1 p q)
        (genLoopTransAtPath 1 α β) =
      GenLoop.transAt (1 : Fin (m + 2)).succ
        (genLoopNormalizedSelfTrackCube (m + 1) p α)
        (genLoopNormalizedSelfTrackCube (m + 1) q β) :=
  genLoopNormalizedSelfTrackCube_transAt (m + 1) 1 (by exact Fin.zero_ne_one.symm) p q α β

end QuillenTest.GenLoopSelfTrackSpatialProduct
