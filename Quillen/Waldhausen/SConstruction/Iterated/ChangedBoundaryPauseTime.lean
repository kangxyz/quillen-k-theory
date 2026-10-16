/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.ChangedBoundaryPauseFaces

/-! The original transRefl time, retaining the required terminal constant half. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
namespace Quillen.SimplexParameters.ChangedBoundaryPause

/-- The exact terminal time used in mathlib's original transRefl construction. -/
def terminalTime : C(unitInterval, unitInterval) :=
  ⟨fun r ↦ ⟨Path.Homotopy.transReflReparamAux r,
    Path.Homotopy.transReflReparamAux_mem_I r⟩, by fun_prop⟩

/-- Interpolate original path time, not points of an arbitrary nerve realization. -/
def time : C(unitInterval × unitInterval, unitInterval) :=
  ⟨fun z ↦ ⟨(unitInterval.symm z.1 : ℝ) * z.2 + (z.1 : ℝ) * terminalTime z.2,
    show (unitInterval.symm z.1 : ℝ) • (z.2 : ℝ) +
      (z.1 : ℝ) • (terminalTime z.2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from
      convex_Icc _ _ z.2.2 (terminalTime z.2).2
        (by unit_interval) (by unit_interval) (by simp)⟩, by fun_prop⟩

/-- The comparison begins at the literal original time. -/
theorem time_zero (r : unitInterval) : time (0, r) = r := by
  apply Subtype.ext
  simp [time]

/-- The terminal time is the exact two-speed terminal pause. -/
theorem time_one (r : unitInterval) : time (1, r) = terminalTime r := by
  apply Subtype.ext
  simp [time]

/-- The initial endpoint stays fixed for every comparison time. -/
theorem time_source (a : unitInterval) : time (a, 0) = 0 := by
  apply Subtype.ext
  simp [time, terminalTime, Path.Homotopy.transReflReparamAux_zero]

/-- The final endpoint stays fixed, with no reversal of the comparison time. -/
theorem time_target (a : unitInterval) : time (a, 1) = 1 := by
  apply Subtype.ext
  simp [time, terminalTime, Path.Homotopy.transReflReparamAux_one]

open Convexity
variable {k : ℕ} {b₀ b₁ : StdSimplex ℝ (Fin (k + 1))} (m : Path b₀ b₁)

/-- The changing edge is exactly the specified transRefl path at its original time. -/
theorem rightEdge_apply (a r : unitInterval) :
    rightEdge (m := m) (a, r) = m (time (a, r)) := by
  unfold rightEdge Path.Homotopy.transRefl
  rw [Path.Homotopy.symm_symm]
  rfl

end Quillen.SimplexParameters.ChangedBoundaryPause
