/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackNull

/-! # Exact supplied-null representative consumer -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u
namespace QuillenTest.GenLoopSelfTrackNull
open Quillen
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Even at the first input degree, the exact supplied null and original track are retained. -/
theorem original_null_degree_one (p : GenLoop (Fin 1) X x) (α : Path p p)
    (Q : Path p GenLoop.const) :
    genLoopSelfTrackClass 0 p α =
      (⟦loopUncurry (genLoopOfBasedPath (Q.symm.trans (α.trans Q)))⟧ :
        HomotopyGroup.Pi 2 X x) :=
  genLoopSelfTrackClass_eq_null_conjugate 0 p α Q

/-- Uncurrying does not reorder the original null-conjugated track's coordinates. -/
theorem original_null_coordinates (m : ℕ) (p : GenLoop (Fin (m + 1)) X x)
    (α : Path p p) (Q : Path p GenLoop.const) (z : Fin (m + 2) → unitInterval) :
    loopUncurry (genLoopOfBasedPath (Q.symm.trans (α.trans Q))) z =
      (Q.symm.trans (α.trans Q)) (z 0) (Fin.tail z) := rfl

end QuillenTest.GenLoopSelfTrackNull
