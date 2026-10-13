/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.NeighborhoodContraction

/-! # Independent actual-point ambient-neighborhood consumer -/

@[expose] public section
noncomputable section
open Set Topology Quillen.ClassicalCW
universe u
namespace Consumer.CWGlobalNeighborhood
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

/-- Every original point has an actual open ambient-contractible neighborhood,
without finite dimension, local finiteness, countability or supplied local geometry. -/
theorem exists_original_point_contraction (x : C) :
    ∃ U : Set C, IsOpen U ∧ x ∈ U ∧
      Nonempty ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, C)).Homotopy
        (ContinuousMap.const U x)) := by
  obtain ⟨n, i, y, hy⟩ := exists_cellNeighborhood C x
  have he : cellNeighborhoodToComplex C n i y = x := Subtype.ext hy
  refine ⟨neighborhoodSet C n i, isOpen_neighborhoodSet C n i, ?_, ?_⟩
  · rw [← he]
    exact seed_mem_neighborhoodSet C n i y
  · have H := neighborhoodAmbientContraction C n i y
    rw [he] at H
    exact ⟨H⟩

end Consumer.CWGlobalNeighborhood
