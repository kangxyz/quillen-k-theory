/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.NeighborhoodContraction

/-! # Original-topology global neighborhood regressions -/

@[expose] public section
noncomputable section
open Set Topology Quillen.ClassicalCW
open scoped unitInterval
universe u
namespace QuillenTest.CWGlobalNeighborhood
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C n)

/-- The union is open in the original entire CW subtype, not just in each skeleton. -/
theorem actual_ambient_open : IsOpen (neighborhoodSet C n i) := isOpen_neighborhoodSet C n i

/-- Each original characteristic disk has exactly its prescribed finite-stage preimage. -/
theorem exact_disk_preimage (m : ℕ) (j : RelCWComplex.cell C m) :
    (fun z : CharacteristicDisk m ↦ characteristicQuotient C ⟨m, j, z⟩) ⁻¹'
      neighborhoodSet C n i =
    (characteristicToSkeleton C j (Nat.lt_add_of_pos_left (Nat.succ_pos n))) ⁻¹'
      skeletalNeighborhood C n i m := neighborhoodSet_characteristic_preimage C n i m j

/-- Restricting the actual quotient to the proved-open union retains the quotient topology. -/
theorem open_restricted_quotient :
    IsQuotientMap ((neighborhoodSet C n i).restrictPreimage (characteristicQuotient C)) :=
  isQuotientMap_neighborhood_restrict C n i

/-- The explicit restricted-disk presentation is itself a genuine quotient. -/
theorem restricted_disk_quotient : IsQuotientMap (neighborhoodCharacteristicMap C n i) :=
  isQuotientMap_neighborhoodCharacteristicMap C n i

variable (x : CellNeighborhood C n i)

/-- The original chosen point belongs to the ambient union. -/
theorem original_seed_membership : cellNeighborhoodToComplex C n i x ∈ neighborhoodSet C n i :=
  seed_mem_neighborhoodSet C n i x

/-- The initial endpoint is exactly the original subtype inclusion. -/
theorem exact_initial_endpoint (y : Neighborhood C n i) :
    neighborhoodAmbientContraction C n i x (0, y) = y.val :=
  (neighborhoodAmbientContraction C n i x).apply_zero y

/-- The final endpoint is the prescribed original point. -/
theorem exact_terminal_endpoint (y : Neighborhood C n i) :
    neighborhoodAmbientContraction C n i x (1, y) = cellNeighborhoodToComplex C n i x :=
  (neighborhoodAmbientContraction C n i x).apply_one y

/-- Global restriction does not alter the time parameter of any finite stage. -/
theorem unchanged_time_stage (k : ℕ) (t : I) (y : SkeletalNeighborhood C n i k) :
    neighborhoodAmbientContraction C n i x (t, neighborhoodStageInclusion C n i k y) =
      (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) :=
  neighborhoodAmbientContraction_stage C n i x k t y

/-- The global map is continuous for the actual product topology, including time zero. -/
theorem actual_joint_continuity : Continuous (neighborhoodContractionFun C n i x) :=
  continuous_neighborhoodContractionFun C n i x

end QuillenTest.CWGlobalNeighborhood
