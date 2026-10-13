/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.SkeletonNeighborhoodDeformation

/-! # Actual neighborhood attachment and deformation regressions -/

@[expose] public section
noncomputable section
open Set Topology Quillen.ClassicalCW
open scoped unitInterval
universe u
namespace QuillenTest.CWSkeletonNeighborhood
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

/-- No new disk collar can be attached over the empty old neighborhood. -/
theorem empty_enlargement (n : ℕ) : stepNeighborhood C n ∅ = ∅ := by
  have he : stepNeighborhoodSource C n ∅ = ∅ := by
    ext z
    cases z with
    | inl x => simp [stepNeighborhoodSource]
    | inr z =>
      simp [stepNeighborhoodSource, stepCollarDirections, radialCollarSet_empty]
  simp [stepNeighborhood, he]

/-- The initial empty skeleton and empty zero-sphere produce an empty collar enlargement. -/
theorem zero_step_empty (U : Set (SkeletonLT C 0)) : stepNeighborhood C 0 U = ∅ := by
  let := skeletonLT_zero_isEmpty C
  have hU : U = ∅ := Subsingleton.elim _ _
  rw [hU]
  exact empty_enlargement C 0

/-- Old points are included exactly when they were in the prescribed old neighborhood. -/
theorem exact_old_intersection (n : ℕ) (U : Set (SkeletonLT C n)) :
    (skeletonInclusion C n) ⁻¹' stepNeighborhood C n U = U := by
  ext x
  exact skeletonInclusion_mem_stepNeighborhood C n U x

/-- The original characteristic disk sees exactly its literal half-radius collar. -/
theorem exact_disk_preimage (n : ℕ) (U : Set (SkeletonLT C n)) (i : RelCWComplex.cell C n) :
    (skeletonCharacteristicMap C n i) ⁻¹' stepNeighborhood C n U =
      radialCollarSet n (stepCollarDirections C n U i) := by
  ext z
  exact skeletonCharacteristicMap_mem_stepNeighborhood C n U i z

variable (n : ℕ) (U : Set (SkeletonLT C n)) (hU : IsOpen U)

/-- The actual retraction is a literal left inverse to the original neighborhood inclusion. -/
theorem actual_left_inverse : Function.LeftInverse (stepNeighborhoodRetraction C n U hU)
    (stepNeighborhoodInclusion C n U hU) := stepNeighborhoodRetraction_old C n U hU

/-- Every old point is fixed for the entire time interval, not just at the endpoints. -/
theorem fixed_old_at_all_times (t : I) (x : U) :
    stepNeighborhoodDeformation C n U hU (t, stepNeighborhoodInclusion C n U hU x) =
      stepNeighborhoodInclusion C n U hU x := stepNeighborhoodDeformation_fixed C n U hU t x

/-- The original point is the initial value of the constructed deformation. -/
theorem exact_initial_value (y : stepNeighborhood C n U) :
    stepNeighborhoodDeformation C n U hU (0, y) = y :=
  (stepNeighborhoodDeformation C n U hU).apply_zero y

/-- The final value is the original inclusion of the constructed retraction. -/
theorem exact_final_value (y : stepNeighborhood C n U) :
    stepNeighborhoodDeformation C n U hU (1, y) =
      stepNeighborhoodInclusion C n U hU (stepNeighborhoodRetraction C n U hU y) :=
  (stepNeighborhoodDeformation C n U hU).apply_one y

/-- The complete collar path is the unchanged original radial formula. -/
theorem exact_collar_track (t : I) (i : RelCWComplex.cell C n)
    (z : RadialCollar n (stepCollarDirections C n U i)) :
    stepNeighborhoodDeformation C n U hU (t, stepNeighborhoodCollarMap C n U hU i z) =
      stepNeighborhoodCollarMap C n U hU i
        (collarRadialMap n (stepCollarDirections C n U i) (t, z)) :=
  stepNeighborhoodDeformationFun_collar C n U hU t i z

/-- The product topology, rather than only separate continuity, is checked. -/
theorem actual_joint_continuity :
    Continuous (fun p : I × stepNeighborhood C n U ↦ stepNeighborhoodDeformation C n U hU p) :=
  (stepNeighborhoodDeformation C n U hU).continuous_toFun

end QuillenTest.CWSkeletonNeighborhood
