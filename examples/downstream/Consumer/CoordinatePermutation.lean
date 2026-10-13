/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.CoordinatePermutation

/-! # Independent consumer of the actual time-first coordinate sign -/

public section

noncomputable section

open Quillen
open scoped Topology unitInterval

namespace Consumer.CoordinatePermutation

universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The H3 side convention simultaneously has the exact coordinate formula
and the correct additive class coefficient in every degree at least two. -/
theorem timeFirstFormulaAndClass (n : ℕ) (k : Fin (n + 2)) (p : GenLoop (Fin (n + 2)) X x) :
    (∀ t, permuteGenLoop k.cycleRange.symm p t =
      p (Fin.cons (t k) (k.removeNth t))) ∧
    Additive.ofMul (genLoopClass (permuteGenLoop k.cycleRange.symm p)) =
      ((-1 : ℤ) ^ k.val) • Additive.ofMul (genLoopClass p) :=
  ⟨permuteGenLoop_cycleRange_symm_apply k p,
    permuteGenLoop_cycleRange_symm_additiveClass k p⟩

/-- This class is literally the existing cubical homotopy quotient. -/
theorem originalQuotientClass (n : ℕ) (p : GenLoop (Fin n) X x) :
    genLoopClass p = (Quotient.mk' p : HomotopyGroup.Pi n X x) := rfl

end Consumer.CoordinatePermutation
