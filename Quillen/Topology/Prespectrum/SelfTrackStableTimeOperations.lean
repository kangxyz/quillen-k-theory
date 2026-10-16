/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackStableOperation
public import Quillen.Topology.Prespectrum.SelfTrackTimeOperations

/-! # Literal reversal on the original integer-graded stable self-track operation -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Reversing the actual track negates its unchanged stable-stage map. -/
theorem Homotopy.stableStageOperation_symm (H : Homotopy f f) (d : ℤ) (n : ℕ) :
    H.symm.stableStageOperation d n = -H.stableStageOperation d n := by
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul
    (H.homotopyClassOperation_symm ((-d).toNat + n + 2) (d.toNat + n + 1)
      (Additive.toMul a))

/-- Reversal negates the actual colimit operation without altering its signs or tail offset. -/
theorem Homotopy.stableOperation_symm (H : Homotopy f f) (d : ℤ) :
    H.symm.stableOperation d = -H.stableOperation d := by
  apply colimit.hom_ext
  intro n
  change stableHomotopyι E d n ≫ H.symm.stableOperation d =
    stableHomotopyι E d n ≫ (-H.stableOperation d)
  rw [Preadditive.comp_neg, H.symm.stableOperation_ι, H.stableOperation_ι,
    H.stableStageOperation_symm]
  simp only [smul_neg, Preadditive.neg_comp]

end Quillen.LoopPrespectrum
