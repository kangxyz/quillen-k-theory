/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.CellNeighborhood

/-!
# An actual local seed at every original CW point

This independent client packages the selected open-skeleton neighborhood,
original point, and its joint continuous ambient contraction. No global open
neighborhood or whole-complex cover is asserted by this finite-stage client.
-/

@[expose] public section
noncomputable section
open Set Topology Quillen.ClassicalCW
open scoped unitInterval
universe u
namespace Consumer.CWNeighborhoodSeed

/-- Every original point has an open seed in its first cell-containing skeleton,
with the exact prescribed ambient endpoint and the whole initial waiting interval. -/
theorem exists_original_seed {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] (x : C) :
    ∃ (n : ℕ) (i : RelCWComplex.cell C n) (y : CellNeighborhood C n i),
      IsOpen (cellNeighborhoodSet C n i) ∧ cellNeighborhoodToComplex C n i y = x ∧
      ∃ H : (cellNeighborhoodToComplex C n i).Homotopy
          (ContinuousMap.const (CellNeighborhood C n i) x),
        ∀ (t : I) (z : CellNeighborhood C n i), (t : ℝ) ≤ 1 / 2 →
          H (t, z) = cellNeighborhoodToComplex C n i z := by
  obtain ⟨n, i, y, hy⟩ := exists_cellNeighborhood C x
  have he : cellNeighborhoodToComplex C n i y = x := Subtype.ext hy
  refine ⟨n, i, y, isOpen_cellNeighborhoodSet C n i, he, ?_⟩
  subst x
  exact ⟨cellNeighborhoodAmbientContraction C n i y,
    fun t z ht ↦ cellNeighborhoodAmbientContraction_stationary C n i y z t ht⟩

end Consumer.CWNeighborhoodSeed
