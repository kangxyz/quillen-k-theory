/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.Loop.NormalizedSelfTrackNaturality

/-! Exact point-set naturality of the retained original normalized self-track. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open Quillen
universe u v
namespace QuillenTest.LoopNormalizedSelfTrackNaturality

/-- The original whole normalized path commutes with the original based continuous map. -/
theorem original_normalized_path_naturality {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (h : f x = y) (γ : Path x x) (α : Path γ γ) :
    basedLoopMap (basedLoopMap f h) (basedLoopMap_refl f h)
        (loopNormalizedSelfTrack γ α) =
      loopNormalizedSelfTrack (basedLoopMap f h γ)
        (α.map (basedLoopMap f h).continuous) := loopNormalizedSelfTrack_naturality f h γ α

end QuillenTest.LoopNormalizedSelfTrackNaturality
