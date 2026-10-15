/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH1Components

/-! Exact cell coordinates of the unchanged native concatenation, including shared boundaries. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.NativePathCells

/-- The affine parameter map `t ↦ t / 2` into the first half of the unit interval. -/
def lower : C(unitInterval, unitInterval) :=
  ⟨fun t ↦ ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, by fun_prop⟩
/-- The affine parameter map `t ↦ (t + 1) / 2` into the second half of the unit interval. -/
def upper : C(unitInterval, unitInterval) :=
  ⟨fun t ↦ ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, by fun_prop⟩

/-- Both native half intervals cover the entire original parameter, not a sampled subset. -/
theorem cover (s : unitInterval) : (∃ t, lower t = s) ∨ (∃ t, upper t = s) := by
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · refine Or.inl ⟨⟨2 * (s : ℝ), by constructor <;> linarith [s.2.1]⟩, ?_⟩
    apply Subtype.ext
    dsimp [lower]
    ring
  · refine Or.inr ⟨⟨2 * (s : ℝ) - 1, by constructor <;> linarith [s.2.2]⟩, ?_⟩
    apply Subtype.ext
    dsimp [upper]
    ring

/-- The actual three-piece right-associated path covers its original whole time interval. -/
theorem three_cover (s : unitInterval) :
    (∃ t, lower t = s) ∨ (∃ t, upper (lower t) = s) ∨ (∃ t, upper (upper t) = s) := by
  rcases cover s with hs | ⟨t, rfl⟩
  · exact Or.inl hs
  · rcases cover t with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · exact Or.inr (Or.inl ⟨r, rfl⟩)
    · exact Or.inr (Or.inr ⟨r, rfl⟩)

end Quillen.NativePathCells
namespace Quillen.LoopPrespectrum.Homotopy
open Quillen.NativePathCells
variable {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F}
  (H : Homotopy f g) (K : Homotopy g h)

/-- Every point of the original first half is exactly the first homotopy at its native speed. -/
theorem trans_lower_cell (n : ℕ) (s : unitInterval) (x : E.space n) :
    (H.trans K).level n (lower s, x) = H.level n (s, x) := by
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (lower s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · change H.level n (⟨2 * (lower s : ℝ), _⟩, x) = H.level n (s, x)
    exact congrArg (fun t : unitInterval ↦ H.level n (t, x))
      (Subtype.ext (by dsimp [lower]; ring))
  · rename_i hs
    exfalso
    apply hs
    change (s : ℝ) / 2 ≤ 1 / 2
    linarith [s.2.2]

/-- The entire second half, including its shared initial point, retains the second native track. -/
theorem trans_upper_cell (n : ℕ) (s : unitInterval) (x : E.space n) :
    (H.trans K).level n (upper s, x) = K.level n (s, x) := by
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (upper s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · rename_i hs
    have hs₀ : s = 0 := by
      apply Subtype.ext
      change ((s : ℝ) + 1) / 2 ≤ 1 / 2 at hs
      change (s : ℝ) = 0
      linarith [s.2.1]
    subst s
    change H.level n (⟨2 * (upper 0 : ℝ), _⟩, x) = K.level n (0, x)
    calc
      _ = H.level n (1, x) := congrArg (fun t : unitInterval ↦ H.level n (t, x))
        (Subtype.ext (by norm_num [upper]))
      _ = _ := (H.at_one n x).trans (K.at_zero n x).symm
  · change K.level n (⟨2 * (upper s : ℝ) - 1, _⟩, x) = K.level n (s, x)
    exact congrArg (fun t : unitInterval ↦ K.level n (t, x))
      (Subtype.ext (by dsimp [upper]; ring))

end Quillen.LoopPrespectrum.Homotopy
