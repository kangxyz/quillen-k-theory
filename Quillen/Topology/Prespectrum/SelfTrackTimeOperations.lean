/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackTimeOperations
public import Quillen.Topology.Prespectrum.SelfTrackHomotopyClass

/-! # Original self-track reversal and concatenation on finite homotopy classes -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology
universe u
namespace Quillen.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Literal reversal negates the original finite self-track class, including input Pi-one. -/
theorem Homotopy.homotopyClassOperation_symm (H : Homotopy f f) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    H.symm.homotopyClassOperation n m a = (H.homotopyClassOperation n m a)⁻¹ := by
  induction a using Quotient.inductionOn with
  | h p =>
    simp only [Homotopy.homotopyClassOperation_mk, Homotopy.genLoopPath_symm,
      genLoopSelfTrackClass_symm]

/-- The actual interval concatenation gives the reversed track-group product. -/
theorem Homotopy.homotopyClassOperation_trans (H K : Homotopy f f) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    (H.trans K).homotopyClassOperation n m a =
      K.homotopyClassOperation n m a * H.homotopyClassOperation n m a := by
  induction a using Quotient.inductionOn with
  | h p =>
    simp only [Homotopy.homotopyClassOperation_mk, Homotopy.genLoopPath_trans,
      genLoopSelfTrackClass_trans]

end Quillen.LoopPrespectrum
