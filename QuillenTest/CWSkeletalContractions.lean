/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.SkeletalNeighborhoodContractions

/-! # Same-time skeletal contraction regressions -/

@[expose] public section
noncomputable section
open Set Topology Quillen Quillen.ClassicalCW
open scoped unitInterval
universe u
namespace QuillenTest.CWSkeletalContractions
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C n)

/-- Stage zero is the original open cell, including the zero-dimensional case. -/
theorem actual_seed : skeletalNeighborhood C n i 0 = cellNeighborhoodSet C n i := rfl

/-- Each finite stage is genuinely open in its original strict skeleton. -/
theorem actual_stage_open (k : ℕ) : IsOpen (skeletalNeighborhood C n i k) :=
  isOpen_skeletalNeighborhood C n i k

/-- The exact previous-stage intersection survives every radial enlargement. -/
theorem exact_previous_stage (k : ℕ) :
    (skeletonInclusion C (n + 1 + k)) ⁻¹' skeletalNeighborhood C n i (k + 1) =
      skeletalNeighborhood C n i k := skeletalNeighborhood_preimage_succ C n i k

/-- The stage maps preserve the original ambient points literally. -/
theorem actual_stage_points {k l : ℕ} (h : k ≤ l) (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodInclusion C n i h y).val.val = y.val.val := rfl

/-- The dyadic schedule always leaves a strictly positive waiting interval. -/
theorem positive_wait (k : ℕ) : 0 < dyadicWait k := dyadicWait_pos k

/-- Consecutive waiting times leave a nonempty radial-motion interval. -/
theorem strict_wait (k : ℕ) : dyadicWait (k + 1) < dyadicWait k := dyadicWait_succ_lt k

variable (x : CellNeighborhood C n i)

/-- The initial endpoint is the original inclusion at every finite stage. -/
theorem original_initial_endpoint (k : ℕ) (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodContraction C n i x k).toHomotopy (0, y) =
      skeletalNeighborhoodToComplex C n i k y :=
  skeletalNeighborhoodContraction_zero C n i x k y

/-- Every stage contracts to the same prescribed original point. -/
theorem prescribed_terminal_endpoint (k : ℕ) (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodContraction C n i x k).toHomotopy (1, y) =
      cellNeighborhoodToComplex C n i x := skeletalNeighborhoodContraction_one C n i x k y

/-- The whole closed waiting interval is stationary, including its seam. -/
theorem stationary_initial_interval (k : ℕ) (t : I) (y : SkeletalNeighborhood C n i k)
    (ht : (t : ℝ) ≤ dyadicWait k) :
    (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) =
      skeletalNeighborhoodToComplex C n i k y :=
  skeletalNeighborhoodContraction_stationary C n i x k t y ht

/-- No time reparametrization occurs when passing to any later stage. -/
theorem literal_same_time {k l : ℕ} (h : k ≤ l) (t : I)
    (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodContraction C n i x l).toHomotopy
      (t, skeletalNeighborhoodInclusion C n i h y) =
        (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) :=
  skeletalNeighborhoodContraction_restrict C n i x h t y

/-- Unordered stage representatives of one point give equal values at the same time. -/
theorem representative_independence {k l : ℕ} (y : SkeletalNeighborhood C n i k)
    (z : SkeletalNeighborhood C n i l)
    (h : skeletalNeighborhoodToComplex C n i k y = skeletalNeighborhoodToComplex C n i l z)
    (t : I) :
    (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) =
      (skeletalNeighborhoodContraction C n i x l).toHomotopy (t, z) :=
  skeletalNeighborhoodContraction_eq_of_toComplex_eq C n i x y z h t

/-- Joint continuity holds on the original product topology at every stage. -/
theorem joint_continuity (k : ℕ) :
    Continuous (fun p : I × SkeletalNeighborhood C n i k ↦
      (skeletalNeighborhoodContraction C n i x k).toHomotopy p) :=
  (skeletalNeighborhoodContraction C n i x k).toHomotopy.continuous_toFun

end QuillenTest.CWSkeletalContractions
