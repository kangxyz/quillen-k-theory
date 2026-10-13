/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.SimplexStraighteningStep

/-! # Independent checks for actual finite simplex straightening adapters -/

public section

open Convexity
open scoped Topology unitInterval

universe u

namespace Consumer

-- The endpoint equation is a consequence of an actual homotopy, at every simplex point.
theorem actual_low_dimensional_filling {Z : Type u} [TopologicalSpace Z]
    (n d : ℕ) (hd : d < n) (z : Z)
    (hs : ∀ x : Z, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (f : C(StdSimplex ℝ (Fin (d + 1)), Z))
    (H : C(Quillen.simplexBoundary d × I, Z))
    (hzero : ∀ b : Quillen.simplexBoundary d, H (b, 0) = f b.val)
    (hone : ∀ b : Quillen.simplexBoundary d, H (b, 1) = z) :
    ∃ K : f.Homotopy (ContinuousMap.const _ z),
      (∀ (b : Quillen.simplexBoundary d) (t : I), K (t, b.val) = H (b, t)) ∧
      (∀ x, K (0, x) = f x) ∧ ∀ x, K (1, x) = z := by
  obtain ⟨K, hK⟩ := Quillen.exists_simplex_homotopy_of_boundary d (fun x ↦ hs x d hd)
    f (ContinuousMap.const _ z) H hzero hone
  exact ⟨K, hK, K.map_zero_left, K.map_one_left⟩

end Consumer
