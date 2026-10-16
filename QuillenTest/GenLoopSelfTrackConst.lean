/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackConst

/-! # Literal constant-cube self-track consumers -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u
namespace QuillenTest.GenLoopSelfTrackConst
open Quillen
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The least supported input degree still keeps the actual uncurried path class. -/
theorem original_degree_one
    (α : Path (GenLoop.const : GenLoop (Fin 1) X x) GenLoop.const) :
    genLoopSelfTrackClass 0 GenLoop.const α =
      (⟦loopUncurry (genLoopOfBasedPath α)⟧ : HomotopyGroup.Pi 2 X x) :=
  genLoopSelfTrackClass_const 0 α

/-- Track time is exactly the new first coordinate, with original coordinates in order. -/
theorem original_track_coordinates (m : ℕ)
    (α : Path (GenLoop.const : GenLoop (Fin (m + 1)) X x) GenLoop.const)
    (z : Fin (m + 2) → unitInterval) :
    loopUncurry (genLoopOfBasedPath α) z = α (z 0) (Fin.tail z) := rfl

end QuillenTest.GenLoopSelfTrackConst
