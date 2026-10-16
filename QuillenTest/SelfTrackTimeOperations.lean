/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackTimeOperations

/-! # Low-degree consumers of literal self-track time operations -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology
universe u
namespace QuillenTest.SelfTrackTimeOperations
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Reversal applies already to a supplied original Pi-one class. -/
theorem pi_one_reversal (H : Homotopy f f) (n : ℕ)
    (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    H.symm.homotopyClassOperation n 0 a = (H.homotopyClassOperation n 0 a)⁻¹ :=
  H.homotopyClassOperation_symm n 0 a

/-- Original concatenation retains its interval halves and product order. -/
theorem pi_one_concatenation (H K : Homotopy f f) (n : ℕ)
    (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    (H.trans K).homotopyClassOperation n 0 a =
      K.homotopyClassOperation n 0 a * H.homotopyClassOperation n 0 a :=
  H.homotopyClassOperation_trans K n 0 a

end QuillenTest.SelfTrackTimeOperations
