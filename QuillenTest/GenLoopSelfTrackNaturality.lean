/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackNaturality

/-! Based naturality retains the original normalized representative. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open Quillen
universe u v
namespace QuillenTest.GenLoopSelfTrackNaturality

/-- The actual cube, including both cancellations, is natural under the supplied based map. -/
theorem original_normalized_cube_postcomp
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α : Path p p) :
    genLoopPostcomp f h (genLoopNormalizedSelfTrackCube m p α) =
      genLoopNormalizedSelfTrackCube m (genLoopPostcomp f h p)
        (α.map (genLoopPostcompContinuousMap f h).continuous) :=
  genLoopNormalizedSelfTrackCube_naturality f h m p α

end QuillenTest.GenLoopSelfTrackNaturality
