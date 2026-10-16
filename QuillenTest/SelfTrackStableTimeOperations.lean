/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackStableTimeOperations
public import QuillenTest.SelfTrackTimeOperations

/-! # Negative-degree consumers of literal stable track reversal -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackStableTimeOperations
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Reversal retains the actual negative-one stable group, without an Omega assumption. -/
theorem negative_one_reversal (H : Homotopy f f) :
    H.symm.stableOperation (-1) = -H.stableOperation (-1) :=
  H.stableOperation_symm (-1)

/-- The original degree-zero operation likewise retains its exact sign and tail. -/
theorem zero_reversal (H : Homotopy f f) :
    H.symm.stableOperation 0 = -H.stableOperation 0 :=
  H.stableOperation_symm 0

end QuillenTest.SelfTrackStableTimeOperations
