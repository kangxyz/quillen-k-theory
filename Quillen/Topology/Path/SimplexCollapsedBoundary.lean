/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexLiftOperations

/-! The actual scalar lower edge of the fixed paused chart surface. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity
open scoped Topology unitInterval
namespace Quillen.SimplexParameters
variable {k : ℕ} {a₀ b₀ a₁ b₁ : StdSimplex ℝ (Fin (k + 1))}

/-- Native three-side collapse retains the exact left route, including its original speed. -/
theorem collapsed_left_path {p : Path a₀ b₀} {l : Path a₀ a₁}
    {q : Path a₁ b₁} {m : Path b₀ b₁} (J : p.Homotopy ((l.trans q).trans m.symm))
    (r : unitInterval) : collapsed J (r, 0) = l r := by
  rw [← ThreeSideSquare.collapse_leftTime r, collapsed_collapse, J.apply_one]
  change ((l.trans q).trans m.symm) (ThreeSideSquare.leftTime r) = l r
  rw [Path.trans_apply]
  split
  · rw [Path.trans_apply]
    split
    · congr 1
      apply Subtype.ext
      dsimp [ThreeSideSquare.leftTime]
      ring
    · rename_i h
      exfalso
      apply h
      dsimp [ThreeSideSquare.leftTime]
      linarith [r.2.2]
  · rename_i h
    exfalso
    apply h
    dsimp [ThreeSideSquare.leftTime]
    linarith [r.2.2]

end Quillen.SimplexParameters
