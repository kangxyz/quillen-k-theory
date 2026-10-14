/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Topology.Path.SimplexCollapsedBoundary

/-! All four scalar edge paths of the exact original H0 cylinder face. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity Quillen.SimplexParameters
open scoped Topology unitInterval
namespace Quillen.SimplexParameters
variable {k : ℕ} {a₀ b₀ a₁ b₁ : StdSimplex ℝ (Fin (k + 1))}
variable {p : Path a₀ b₀} {l : Path a₀ a₁} {q : Path a₁ b₁} {m : Path b₀ b₁}

/-- The actual collapse retains the complete original source path. -/
theorem collapsed_zero_path (J : p.Homotopy ((l.trans q).trans m.symm)) (t : unitInterval) :
    collapsed J (0, t) = p t := by
  rw [← ThreeSideSquare.collapse_zero t, collapsed_collapse, J.apply_zero]
  rfl

/-- The middle quarter of the original boundary retains the full top path at its original speed. -/
theorem collapsed_top_path (J : p.Homotopy ((l.trans q).trans m.symm)) (t : unitInterval) :
    collapsed J (1, t) = q t := by
  rw [← ThreeSideSquare.collapse_topTime t, collapsed_collapse, J.apply_one]
  change ((l.trans q).trans m.symm) (ThreeSideSquare.topTime t) = q t
  rw [← Path.extend_apply ((l.trans q).trans m.symm) (ThreeSideSquare.topTime t).property]
  rw [Path.extend_trans_of_le_half _ _ (by
    dsimp [ThreeSideSquare.topTime]
    linarith [t.2.2])]
  rw [Path.extend_trans_of_half_le _ _ (by
    dsimp [ThreeSideSquare.topTime]
    linarith [t.2.1])]
  have he : 2 * (2 * (ThreeSideSquare.topTime t : ℝ)) - 1 = (t : ℝ) := by
    dsimp [ThreeSideSquare.topTime]
    ring
  rw [he, Path.extend_apply _ t.property]

/-- The original final half retains the inverse boundary path as the native right edge. -/
theorem collapsed_right_path (J : p.Homotopy ((l.trans q).trans m.symm)) (r : unitInterval) :
    collapsed J (r, 1) = m r := by
  rw [← ThreeSideSquare.collapse_rightTime r, collapsed_collapse, J.apply_one]
  change ((l.trans q).trans m.symm) (ThreeSideSquare.rightTime r) = m r
  rw [← Path.extend_apply ((l.trans q).trans m.symm) (ThreeSideSquare.rightTime r).property]
  rw [Path.extend_trans_of_half_le _ _ (by
    dsimp [ThreeSideSquare.rightTime]
    linarith [r.2.2]), Path.extend_symm_apply]
  have he : 1 - (2 * (ThreeSideSquare.rightTime r : ℝ) - 1) = (r : ℝ) := by
    dsimp [ThreeSideSquare.rightTime]
    ring
  rw [he, Path.extend_apply _ r.property]

end Quillen.SimplexParameters
