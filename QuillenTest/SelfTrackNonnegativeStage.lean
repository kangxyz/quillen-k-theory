/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackNonnegativeStage

/-! # Original degree-zero stable-stage evaluation -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackNonnegativeStage
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- The nonnegative system's first stage is the genuine second spectrum space. -/
theorem original_degree_zero (H : Homotopy f f)
    (a : HomotopyGroup.Pi 2 (E.space 2) (E.point 2)) :
    H.stableOperation 0 (stableHomotopyι E 0 0
        (nonnegativeStableStageEquiv E 0 (Additive.ofMul a))) =
      stableHomotopyι F 1 0
        (nonnegativeStableStageEquiv F 1
          (Additive.ofMul (H.homotopyClassOperation 2 1 a))) :=
  H.stableOperation_nonnegative_stage 0 a

end QuillenTest.SelfTrackNonnegativeStage
