/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.CoordinatePermutation

/-! # Coordinate action, low-degree, direction, and parity regressions -/

public section

noncomputable section

open Quillen
open scoped Topology unitInterval

namespace QuillenTest.CoordinatePermutation

universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Degree zero has an actual action, without installing a nonexistent group. -/
theorem degreeZeroAction (π : Equiv.Perm (Fin 0)) (p : GenLoop (Fin 0) X x) :
    permuteGenLoop π p = p :=
  permuteGenLoop_of_subsingleton π p

/-- Every degree-one coordinate permutation is literally trivial. -/
theorem degreeOneAction (π : Equiv.Perm (Fin 1)) (p : GenLoop (Fin 1) X x) :
    permuteGenLoop π p = p :=
  permuteGenLoop_of_subsingleton π p

/-- The two-coordinate swap contributes inversion in the original homotopy group. -/
theorem swapClassInverse (p : GenLoop (Fin 2) X x) :
    genLoopClass (permuteGenLoop (Equiv.swap (0 : Fin 2) 1) p) = (genLoopClass p)⁻¹ := by
  simpa using permuteGenLoop_class (Equiv.swap (0 : Fin 2) 1) p

/-- A first-slot range cycle does not change the class. -/
theorem firstSlotClass (p : GenLoop (Fin 3) X x) :
    genLoopClass (permuteGenLoop (0 : Fin 3).cycleRange.symm p) = genLoopClass p := by
  simpa using permuteGenLoop_cycleRange_symm_class (0 : Fin 3) p

/-- Moving time across one coordinate contributes a minus sign. -/
theorem oddSlotClass (p : GenLoop (Fin 3) X x) :
    Additive.ofMul (genLoopClass (permuteGenLoop (1 : Fin 3).cycleRange.symm p)) =
      -Additive.ofMul (genLoopClass p) := by
  simpa using permuteGenLoop_cycleRange_symm_additiveClass (1 : Fin 3) p

/-- Moving time across two coordinates restores the positive sign. -/
theorem evenSlotClass (p : GenLoop (Fin 3) X x) :
    genLoopClass (permuteGenLoop (2 : Fin 3).cycleRange.symm p) = genLoopClass p := by
  simpa using permuteGenLoop_cycleRange_symm_class (2 : Fin 3) p

/-- The coordinate composition order is checked on actual loops. -/
theorem actualCompositionOrder (π ρ : Equiv.Perm (Fin 3)) (p : GenLoop (Fin 3) X x) :
    permuteGenLoop (π * ρ) p = permuteGenLoop π (permuteGenLoop ρ p) :=
  permuteGenLoop_mul π ρ p

/-- The inverse cycle puts time first in the canonical side-face coordinates. -/
theorem inverseCycleDirection (p : GenLoop (Fin 3) X x) (t : Fin 3 → I) :
    permuteGenLoop (2 : Fin 3).cycleRange.symm p t =
      p (Fin.cons (t 2) ((2 : Fin 3).removeNth t)) :=
  permuteGenLoop_cycleRange_symm_apply 2 p t

/-- Actual homotopy reparametrization preserves both endpoints and the boundary. -/
theorem homotopyEndpoints (π : Equiv.Perm (Fin 3)) {p q : GenLoop (Fin 3) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 3))) (t : Fin 3 → I) :
    permuteGenLoopHomotopy π H (0, t) = permuteGenLoop π p t ∧
      permuteGenLoopHomotopy π H (1, t) = permuteGenLoop π q t :=
  ⟨(permuteGenLoopHomotopy π H).apply_zero t, (permuteGenLoopHomotopy π H).apply_one t⟩

end QuillenTest.CoordinatePermutation
