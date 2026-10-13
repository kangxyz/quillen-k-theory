/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.HomotopyGroups.Loop.Reversal

/-! # Regression tests for geometric reversal and its actual homotopy action -/
@[expose] public section

noncomputable section
open Quillen
open scoped Topology unitInterval
universe u v
namespace QuillenTest.LoopReversal

open Quillen

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y}

/-- The upstream canonical homeomorphism has exactly the standard reversal map. -/
theorem upstream_homeomorph_forward :
    (loopReversalHomeomorph x : C(Path x x, Path x x)) = loopReversal := rfl

/-- The canonical inverse reverses the same actual loop parameter. -/
theorem upstream_homeomorph_inverse (γ : Path x x) (t : unitInterval) :
    (loopReversalHomeomorph x).symm γ t = γ (unitInterval.symm t) := rfl

/-- An actual path between loops remains a path between their actual reversed
images, even when the loops belong to nonconstant components. -/
theorem reverse_path_after_based_map (f : C(X, Y)) (hf : f x = y)
    {γ δ : Path x x} (p : Path γ δ) (s t : unitInterval) :
    loopReversalPath (p.map (basedLoopMap f hf).continuous) s t =
      f (p s (unitInterval.symm t)) := rfl

/-- Applying the same geometric normalization twice strictly recovers the
original map on every loop. -/
theorem reverse_twice_recovers_map (f : C(X, Y)) (hf : f x = y) :
    loopReversal.comp ((basedLoopMap f hf).comp loopReversal) = basedLoopMap f hf := by
  apply ContinuousMap.ext
  intro γ
  change loopReversal (basedLoopMap f hf (loopReversal γ)) = basedLoopMap f hf γ
  rw [basedLoopMap_loopReversal]
  exact loopReversal_involutive _

/-- Outer degree zero retains the fundamental group's order-reversing inverse;
no abelian hypothesis is silently introduced. -/
theorem degree_zero_reverses_product (a b : HomotopyGroup.Pi 1 X x) :
    (loopShiftEquiv (x := x) 0).symm
      (homotopyGroupMap loopReversal loopReversal_refl (loopShiftEquiv 0 (a * b))) =
      b⁻¹ * a⁻¹ := by
  rw [loopShiftEquiv_symm_loopReversal, Equiv.symm_apply_apply, mul_inv_rev]

/-- An abelian comparison of the degree-zero loop components obtains its sign
from the actual continuous reversal. This is the shape used for a Q/K₀ label. -/
theorem degree_zero_abelian_label {A : Type v} [CommGroup A]
    (label : HomotopyGroup.Pi 1 X x →* A)
    (a : HomotopyGroup.Pi 0 (Path x x) (Path.refl x)) :
    label ((loopShiftEquiv (x := x) 0).symm
      (homotopyGroupMap loopReversal loopReversal_refl a)) =
      (label ((loopShiftEquiv (x := x) 0).symm a))⁻¹ := by
  rw [loopShiftEquiv_symm_loopReversal, map_inv]

/-- Positive-degree inversion is induced by an actual continuous map and hence
is compatible with the existing loop-space homotopy-group multiplication. -/
theorem positive_inverse_preserves_product (n : ℕ)
    (a b : HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x)) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [← homotopyGroupMap_loopReversal n (a * b),
    ← homotopyGroupMap_loopReversal n a, ← homotopyGroupMap_loopReversal n b]
  exact (piMap n loopReversal loopReversal_refl).map_mul a b

end QuillenTest.LoopReversal
