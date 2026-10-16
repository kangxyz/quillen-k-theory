/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopNormalizedSelfTrackPrefix

/-! Whole-coordinate consumers of the original normalization word, including input degree one. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open scoped Topology unitInterval
open Quillen
universe u
namespace QuillenTest.GenLoopNormalizedSelfTrackPrefix
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Both original cancellations occur in the full path identity. -/
theorem original_complete_prefix_word (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p) :
    genLoopNormalizedSelfTrackPath n p α =
      (GenLoopPrefix.cancellation n p).symm.trans
        ((α.map (GenLoopPrefix.inversePrefix n p).continuous).trans
          (GenLoopPrefix.cancellation n p)) :=
  genLoopNormalizedSelfTrackPath_prefix n p α

/-- Original track time and spatial coordinates remain independent in the whole word. -/
theorem original_prefix_word_coordinates (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p)
    (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    genLoopNormalizedSelfTrackPath n p α t z =
      ((GenLoopPrefix.cancellation n p).symm.trans
        ((α.map (GenLoopPrefix.inversePrefix n p).continuous).trans
          (GenLoopPrefix.cancellation n p))) t z :=
  genLoopNormalizedSelfTrackPath_prefix_apply n p α t z

/-- Input degree one retains the same full path, without any additivity assumption. -/
theorem original_degree_zero_prefix_word (p : GenLoop (Fin 1) X x) (α : Path p p) :
    genLoopNormalizedSelfTrackPath 0 p α =
      (GenLoopPrefix.cancellation 0 p).symm.trans
        ((α.map (GenLoopPrefix.inversePrefix 0 p).continuous).trans
          (GenLoopPrefix.cancellation 0 p)) :=
  genLoopNormalizedSelfTrackPath_prefix 0 p α

/-- The original higher cube curries to the exact original based path family. -/
theorem original_curried_cube (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p) :
    loopCurry (genLoopNormalizedSelfTrackCube n p α) =
      genLoopOfBasedPath (genLoopNormalizedSelfTrackPath n p α) :=
  loopCurry_genLoopNormalizedSelfTrackCube n p α

/-- Every residual coordinate is retained independently of track time. -/
theorem original_curried_coordinates (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p)
    (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    loopCurry (genLoopNormalizedSelfTrackCube n p α) z t =
      genLoopNormalizedSelfTrackPath n p α t z :=
  loopCurry_genLoopNormalizedSelfTrackCube_apply n p α z t

/-- The degree-zero input retains spatial coordinate zero and independent track time. -/
theorem original_degree_zero_coordinates (p : GenLoop (Fin 1) X x) (α : Path p p)
    (s t : unitInterval) :
    loopCurry (genLoopNormalizedSelfTrackCube 0 p α) (fun _ ↦ s) t =
      genLoopNormalizedSelfTrackPath 0 p α t (fun _ ↦ s) :=
  loopCurry_genLoopNormalizedSelfTrackCube_apply 0 p α (fun _ ↦ s) t

/-- The actual spatial boundary stays fixed throughout the original normalized word. -/
theorem original_prefix_word_boundary (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p)
    (t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    ((GenLoopPrefix.cancellation n p).symm.trans
      ((α.map (GenLoopPrefix.inversePrefix n p).continuous).trans
        (GenLoopPrefix.cancellation n p))) t z = x := by
  rw [← genLoopNormalizedSelfTrackPath_prefix]
  exact (genLoopNormalizedSelfTrackPath n p α t).property z hz

/-- Currying retains the whole spatial boundary at every independent track time. -/
theorem original_curried_boundary (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1)))
    (t : unitInterval) :
    loopCurry (genLoopNormalizedSelfTrackCube n p α) z t = x := by
  rw [loopCurry_genLoopNormalizedSelfTrackCube_apply]
  exact (genLoopNormalizedSelfTrackPath n p α t).property z hz

end QuillenTest.GenLoopNormalizedSelfTrackPrefix
