/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ScalarJoins

/-! Continuous concatenation with the exact original half coordinates in either scalar direction. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.ScalarRectangle
variable {X : Type u} [TopologicalSpace X]

section Homotopy
variable {Y : Type*} [TopologicalSpace Y] {f g h : C(Y, X)}
  (F : ContinuousMap.Homotopy f g) (G : ContinuousMap.Homotopy g h)

theorem homotopy_lower (s : unitInterval) (x : Y) :
    (F.trans G) (lower s, x) = F (s, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · change F (⟨2 * (lower s : ℝ), _⟩, x) = F (s, x)
    exact congrArg (fun t : unitInterval ↦ F (t, x))
      (Subtype.ext (by dsimp [lower]; ring))
  · rename_i hs
    exfalso
    apply hs
    change (s : ℝ) / 2 ≤ 1 / 2
    linarith [s.2.2]

theorem homotopy_upper (s : unitInterval) (x : Y) :
    (F.trans G) (upper s, x) = G (s, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · rename_i hs
    have hs₀ : s = 0 := by
      apply Subtype.ext
      change ((s : ℝ) + 1) / 2 ≤ 1 / 2 at hs
      change (s : ℝ) = 0
      linarith [s.2.1]
    subst s
    change F (⟨2 * (upper 0 : ℝ), _⟩, x) = G (0, x)
    calc
      _ = F (1, x) := congrArg (fun t : unitInterval ↦ F (t, x))
        (Subtype.ext (by norm_num [upper]))
      _ = _ := (F.map_one_left x).trans (G.map_zero_left x).symm
  · change G (⟨2 * (upper s : ℝ) - 1, _⟩, x) = G (s, x)
    exact congrArg (fun t : unitInterval ↦ G (t, x))
      (Subtype.ext (by dsimp [upper]; ring))
end Homotopy

variable (F G : C(unitInterval × unitInterval, X))

/-- The continuous slice of `F` obtained by fixing its first coordinate to `s`. -/
def row (s : unitInterval) : C(unitInterval, X) :=
  ⟨fun t ↦ F (s, t), by fun_prop⟩

/-- The homotopy between the first and last slices of `F`, with its first coordinate as homotopy
time.
-/
def rowHomotopy : ContinuousMap.Homotopy (row F 0) (row F 1) where
  toContinuousMap := F
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- Concatenate the actual original surfaces along their proved complete first-coordinate edge. -/
def concatFirst (h : ∀ t, F (1, t) = G (0, t)) : C(unitInterval × unitInterval, X) :=
  ((rowHomotopy F).trans ((rowHomotopy G).cast
    (ContinuousMap.ext (fun t ↦ (h t).symm)) rfl)).toContinuousMap

variable (h : ∀ t, F (1, t) = G (0, t))

theorem concatFirst_lower (s t : unitInterval) :
    concatFirst F G h (lower s, t) = F (s, t) :=
  homotopy_lower (rowHomotopy F) ((rowHomotopy G).cast
    (ContinuousMap.ext (fun t ↦ (h t).symm)) rfl) s t

theorem concatFirst_upper (s t : unitInterval) :
    concatFirst F G h (upper s, t) = G (s, t) :=
  homotopy_upper (rowHomotopy F) ((rowHomotopy G).cast
    (ContinuousMap.ext (fun t ↦ (h t).symm)) rfl) s t

theorem concatFirst_zero (t : unitInterval) : concatFirst F G h (0, t) = F (0, t) :=
  ((rowHomotopy F).trans ((rowHomotopy G).cast
    (ContinuousMap.ext (fun t ↦ (h t).symm)) rfl)).map_zero_left t

theorem concatFirst_one (t : unitInterval) : concatFirst F G h (1, t) = G (1, t) :=
  ((rowHomotopy F).trans ((rowHomotopy G).cast
    (ContinuousMap.ext (fun t ↦ (h t).symm)) rfl)).map_one_left t

/-- The continuous square map obtained by interchanging the two coordinates of `F`. -/
def swap : C(unitInterval × unitInterval, X) := ⟨fun z ↦ F (z.2, z.1), by fun_prop⟩

/-- The same continuous native concatenation in the independent second coordinate. -/
def concatSecond (h : ∀ s, F (s, 1) = G (s, 0)) : C(unitInterval × unitInterval, X) :=
  swap (concatFirst (swap F) (swap G) h)

variable (k : ∀ s, F (s, 1) = G (s, 0))

theorem concatSecond_lower (s t : unitInterval) :
    concatSecond F G k (s, lower t) = F (s, t) :=
  concatFirst_lower (swap F) (swap G) k t s

theorem concatSecond_upper (s t : unitInterval) :
    concatSecond F G k (s, upper t) = G (s, t) :=
  concatFirst_upper (swap F) (swap G) k t s

theorem concatSecond_zero (s : unitInterval) : concatSecond F G k (s, 0) = F (s, 0) :=
  concatFirst_zero (swap F) (swap G) k s

theorem concatSecond_one (s : unitInterval) : concatSecond F G k (s, 1) = G (s, 1) :=
  concatFirst_one (swap F) (swap G) k s

end Quillen.ScalarRectangle
