/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.SkeletalNeighborhoodContractions

/-! # Independent consumer of actual same-time skeletal contractions -/

@[expose] public section
noncomputable section
open Set Topology Quillen Quillen.ClassicalCW
open scoped unitInterval
universe u
namespace Consumer.CWSkeletalContractions
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C n)

/-- Every original cell point admits a concrete family of waiting contractions,
with exact same-time restriction across arbitrary finite stage gaps. -/
theorem exists_compatible_contractions (x : CellNeighborhood C n i) :
    ∃ H : ∀ k, WaitingHomotopy (skeletalNeighborhoodToComplex C n i k)
      (ContinuousMap.const (SkeletalNeighborhood C n i k) (cellNeighborhoodToComplex C n i x))
      (dyadicWait k),
      ∀ (k l : ℕ) (h : k ≤ l) (t : I) (y : SkeletalNeighborhood C n i k),
        (H l).toHomotopy (t, skeletalNeighborhoodInclusion C n i h y) =
          (H k).toHomotopy (t, y) :=
  ⟨skeletalNeighborhoodContraction C n i x,
    fun _ _ h t y ↦ skeletalNeighborhoodContraction_restrict C n i x h t y⟩

end Consumer.CWSkeletalContractions
