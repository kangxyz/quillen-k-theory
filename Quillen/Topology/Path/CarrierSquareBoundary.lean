/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Homotopy.ThreeSideSquare
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Literal three-side boundary and terminal-pause cancellation in an arbitrary carrier

The entire supplied square is retained under the original collapse. Whole path equalities
can rename its boundaries without changing interior values. For a constant right edge,
terminal-pause cancellation is the original Path.Homotopy.transRefl, in its original second
half of homotopy time. No square or filler is selected from endpoint agreement.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Quillen.CarrierPathSquare
variable {X : Type u} [TopologicalSpace X] {a₀ b₀ a₁ b₁ : X}
  {p₀ : Path a₀ b₀} {p₁ : Path a₁ b₁} {l : Path a₀ a₁} {m : Path b₀ b₁}

/-- A carrier-valued square with its four literal path boundaries. -/
structure Square (p₀ : Path a₀ b₀) (p₁ : Path a₁ b₁)
    (l : Path a₀ a₁) (m : Path b₀ b₁) where
  parameter : C(unitInterval × unitInterval, X)
  at_zero (s : unitInterval) : parameter (0, s) = p₀ s
  at_one (s : unitInterval) : parameter (1, s) = p₁ s
  left (r : unitInterval) : parameter (r, 0) = l r
  right (r : unitInterval) : parameter (r, 1) = m r

private theorem path_pasted_left (p : Path a₁ b₁) (l : Path a₀ a₁) (m : Path b₀ b₁)
    (r : unitInterval) :
    ((l.trans p).trans m.symm) (Quillen.ThreeSideSquare.leftTime r) = l r := by
  rw [Path.trans_apply]
  split
  · rw [Path.trans_apply]
    split
    · congr 1
      apply Subtype.ext
      dsimp [Quillen.ThreeSideSquare.leftTime]
      ring
    · rename_i h
      dsimp [Quillen.ThreeSideSquare.leftTime] at h
      linarith [r.2.2]
  · rename_i h
    dsimp [Quillen.ThreeSideSquare.leftTime] at h
    linarith [r.2.2]

private theorem path_pasted_top (p : Path a₁ b₁) (l : Path a₀ a₁) (m : Path b₀ b₁)
    (s : unitInterval) :
    ((l.trans p).trans m.symm) (Quillen.ThreeSideSquare.topTime s) = p s := by
  rw [Path.trans_apply]
  split
  · rw [Path.trans_apply]
    split
    · rename_i h
      have hs : s = 0 := by
        apply Subtype.ext
        change (s : ℝ) = 0
        dsimp [Quillen.ThreeSideSquare.topTime] at h
        linarith [s.2.1]
      subst s
      trans l 1
      · congr 1
        apply Subtype.ext
        norm_num [Quillen.ThreeSideSquare.topTime]
      · exact l.target.trans p.source.symm
    · congr 1
      apply Subtype.ext
      dsimp [Quillen.ThreeSideSquare.topTime]
      ring
  · rename_i h
    dsimp [Quillen.ThreeSideSquare.topTime] at h
    linarith [s.2.2]

private theorem path_pasted_right (p : Path a₁ b₁) (l : Path a₀ a₁) (m : Path b₀ b₁)
    (r : unitInterval) :
    ((l.trans p).trans m.symm) (Quillen.ThreeSideSquare.rightTime r) = m r := by
  rw [Path.trans_apply]
  split
  · rename_i h
    have hr : r = 1 := by
      apply Subtype.ext
      change (r : ℝ) = 1
      dsimp [Quillen.ThreeSideSquare.rightTime] at h
      linarith [r.2.2]
    subst r
    trans (l.trans p) 1
    · congr 1
      apply Subtype.ext
      norm_num [Quillen.ThreeSideSquare.rightTime]
    · exact (l.trans p).target.trans m.target.symm
  · change m (unitInterval.symm _) = _
    congr 1
    apply Subtype.ext
    dsimp [Quillen.ThreeSideSquare.rightTime, unitInterval.symm]
    ring

private theorem boundary_time_cases (s : unitInterval) :
    (∃ r, s = Quillen.ThreeSideSquare.leftTime r) ∨
    (∃ r, s = Quillen.ThreeSideSquare.topTime r) ∨
    (∃ r, s = Quillen.ThreeSideSquare.rightTime r) := by
  by_cases h : (s : ℝ) ≤ 1 / 4
  · left
    refine ⟨⟨4 * s, by constructor <;> linarith [s.2.1]⟩, ?_⟩
    apply Subtype.ext
    dsimp [Quillen.ThreeSideSquare.leftTime]
    ring
  · by_cases h' : (s : ℝ) ≤ 1 / 2
    · right; left
      refine ⟨⟨4 * s - 1, by constructor <;> linarith⟩, ?_⟩
      apply Subtype.ext
      dsimp [Quillen.ThreeSideSquare.topTime]
      ring
    · right; right
      refine ⟨⟨2 - 2 * s, by constructor <;> linarith [s.2.2]⟩, ?_⟩
      apply Subtype.ext
      dsimp [Quillen.ThreeSideSquare.rightTime]
      ring

/-- The actual collapsed upper boundary is the exact original left-associated path pasting. -/
theorem Square.collapse_top (Q : Square p₀ p₁ l m) (s : unitInterval) :
    Q.parameter (Quillen.ThreeSideSquare.collapse (1, s)) =
      ((l.trans p₁).trans m.symm) s := by
  rcases boundary_time_cases s with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [Quillen.ThreeSideSquare.collapse_leftTime]
    exact (Q.left r).trans (path_pasted_left p₁ l m r).symm
  · rw [Quillen.ThreeSideSquare.collapse_topTime]
    exact (Q.at_one r).trans (path_pasted_top p₁ l m r).symm
  · rw [Quillen.ThreeSideSquare.collapse_rightTime]
    exact (Q.right r).trans (path_pasted_right p₁ l m r).symm

/-- Extract the carrier boundary by the same parameter collapse as the native moving square. -/
def Square.toBoundary (Q : Square p₀ p₁ l m) :
    p₀.Homotopy ((l.trans p₁).trans m.symm) where
  toFun z := Q.parameter (Quillen.ThreeSideSquare.collapse z)
  continuous_toFun := Q.parameter.continuous.comp Quillen.ThreeSideSquare.continuous_collapse
  map_zero_left s := by rw [Quillen.ThreeSideSquare.collapse_zero]; exact Q.at_zero s
  map_one_left := Q.collapse_top
  prop' r s hs := by
    change Q.parameter (Quillen.ThreeSideSquare.collapse (r, s)) = p₀ s
    rcases hs with hs | hs
    · subst s
      rw [Quillen.ThreeSideSquare.collapse_left]
      exact Q.at_zero 0
    · subst s
      rw [Quillen.ThreeSideSquare.collapse_right]
      exact Q.at_zero 1

/-- Boundary extraction retains every interior coordinate of the original collapse. -/
theorem Square.toBoundary_apply (Q : Square p₀ p₁ l m) (r s : unitInterval) :
    Q.toBoundary (r, s) = Q.parameter (ThreeSideSquare.collapse (r, s)) := rfl

/-- Whole path equalities rename boundaries, exactly as native ofLevels renames whole levels. -/
def Square.boundaryOfPaths (Q : Square p₀ p₁ l m) {q₀ q₁ : Path a₀ b₀}
    (h₀ : p₀ = q₀) (h₁ : (l.trans p₁).trans m.symm = q₁) : q₀.Homotopy q₁ :=
  Q.toBoundary.cast h₀ h₁

/-- Boundary renaming does not alter either interior time or any carrier point. -/
theorem Square.boundaryOfPaths_apply (Q : Square p₀ p₁ l m) {q₀ q₁ : Path a₀ b₀}
    (h₀ : p₀ = q₀) (h₁ : (l.trans p₁).trans m.symm = q₁) (r s : unitInterval) :
    Q.boundaryOfPaths h₀ h₁ (r, s) = Q.parameter (ThreeSideSquare.collapse (r, s)) := rfl

variable {a b c : X} {old : Path a c} {new : Path b c} {move : Path a b}

/-- Keep the original terminal pause before cancellation, including its full square interior. -/
def Square.pausedConeBoundary (Q : Square old new move (Path.refl c)) :
    old.Homotopy ((move.trans new).trans (Path.refl c)) :=
  Q.boundaryOfPaths rfl (congrArg (fun z : Path c c ↦ (move.trans new).trans z)
    (show (Path.refl c).symm = Path.refl c by ext s; rfl))

/-- Exact carrier counterpart of original conePasting: collapse, boundary cast, then transRefl. -/
def Square.coneBoundary (Q : Square old new move (Path.refl c)) :
    old.Homotopy (move.trans new) :=
  Q.pausedConeBoundary.trans (Path.Homotopy.transRefl (move.trans new))

/-- The first half is the original collapsed square; the second is the original pause removal. -/
theorem Square.coneBoundary_apply (Q : Square old new move (Path.refl c))
    (r s : unitInterval) :
    Q.coneBoundary (r, s) =
      if h : (r : ℝ) ≤ 1 / 2 then
        Q.parameter (ThreeSideSquare.collapse
          (⟨2 * r, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨r.2.1, h⟩⟩, s))
      else
        Path.Homotopy.transRefl (move.trans new)
          (⟨2 * r - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 h).le, r.2.2⟩⟩, s) :=
  Path.Homotopy.trans_apply Q.pausedConeBoundary
    (Path.Homotopy.transRefl (move.trans new)) (r, s)

end Quillen.CarrierPathSquare
