/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopNormalizedSelfTrack

/-! The actual normalized cube retains the original endpoint-fixed self-track class. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open Quillen
universe u
namespace QuillenTest.GenLoopNormalizedSelfTrack

/-- The explicit cube has the originally defined normalized class. -/
theorem original_normalized_cube_class {X : Type u} [TopologicalSpace X] {x : X}
    (m : ℕ) (p : GenLoop (Fin (m + 1)) X x) (α : Path p p) :
    (⟦genLoopNormalizedSelfTrackCube m p α⟧ : HomotopyGroup.Pi (m + 2) X x) =
      genLoopSelfTrackClass m p α := genLoopNormalizedSelfTrackCube_class m p α

/-- The representative of a constant self-track gives the actual identity higher class. -/
theorem original_normalized_refl_cube {X : Type u} [TopologicalSpace X] {x : X}
    (m : ℕ) (p : GenLoop (Fin (m + 1)) X x) :
    (⟦genLoopNormalizedSelfTrackCube m p (Path.refl p)⟧ :
      HomotopyGroup.Pi (m + 2) X x) = (1 : HomotopyGroup.Pi (m + 2) X x) := by
  rw [genLoopNormalizedSelfTrackCube_class, genLoopSelfTrackClass_refl]

end QuillenTest.GenLoopNormalizedSelfTrack
