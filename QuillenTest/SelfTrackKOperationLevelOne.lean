/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationLevelOne
public import QuillenTest.SelfTrackNonnegativeStage

/-! # Original K-zero finite self-track sign consumer -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v
namespace QuillenTest.SelfTrackKOperationLevelOne
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Quillen.Waldhausen.Structure C) (V : Quillen.Waldhausen.Structure D)
variable {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- Original K-zero retains the exact small-model map and the level-one inverse sign. -/
theorem original_kzero_level_one (H : Homotopy f f) (a : W.K 0) :
    V.smallModelKEquiv 1 (originalKSelfTrackOperation W V H 0 a) =
      (H.homotopyClassOperation 1 0 (W.smallModelKEquiv 0 a))⁻¹ :=
  originalKSelfTrackOperation_levelOne W V H 0 a

end QuillenTest.SelfTrackKOperationLevelOne
