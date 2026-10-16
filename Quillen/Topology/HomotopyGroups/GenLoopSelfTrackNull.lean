/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackConst
public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackTransport

/-!
# Self-track classes with a specified original null path

The supplied null path conjugates the original self-track to a based path at
the constant cube. Its literal uncurrying represents the original normalized
class. This does not identify any particular geometric seed or stable map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Quillen
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The actual supplied null path is retained in the higher-class representative. -/
theorem genLoopSelfTrackClass_eq_null_conjugate (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α : Path p p)
    (Q : Path p GenLoop.const) :
    genLoopSelfTrackClass m p α =
      (⟦loopUncurry (genLoopOfBasedPath (Q.symm.trans (α.trans Q)))⟧ :
        HomotopyGroup.Pi (m + 2) X x) := by
  calc
    genLoopSelfTrackClass m p α = genLoopSelfTrackNormalization m GenLoop.const
        (FundamentalGroup.fundamentalGroupMulEquivOfPath Q ⟦α⟧) :=
      (genLoopSelfTrackNormalization_transport m Q ⟦α⟧).symm
    _ = genLoopSelfTrackClass m GenLoop.const (Q.symm.trans (α.trans Q)) := rfl
    _ = _ := genLoopSelfTrackClass_const m _

end Quillen
