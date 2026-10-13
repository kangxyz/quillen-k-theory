/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.SkeletonNeighborhoodDeformation

/-!
# A constructed open strong neighborhood extension

The only geometric input is an open subset of the actual old skeleton.
The open enlargement, original inclusion, retraction and strongly fixed
homotopy are outputs, including when the old neighborhood is empty.
-/

@[expose] public section
noncomputable section
open Set Topology Quillen.ClassicalCW
open scoped unitInterval
universe u
namespace Consumer.CWSkeletonNeighborhood

/-- A genuine next-stage open neighborhood and strong deformation are constructed
without supplied quotient, retraction or homotopy data. -/
theorem exists_actual_neighborhood_extension {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] (n : ℕ) (U : Set (SkeletonLT C n)) (hU : IsOpen U) :
    ∃ W : Set (SkeletonLT C (n + 1)), IsOpen W ∧
      (skeletonInclusion C n) ⁻¹' W = U ∧
      ∃ (j : C(U, W)) (r : C(W, U)),
        (∀ x, (j x).val.val = x.val.val) ∧ Function.LeftInverse r j ∧
        ∃ H : (ContinuousMap.id W).Homotopy (j.comp r),
          ∀ (t : I) (x : U), H (t, j x) = j x := by
  refine ⟨stepNeighborhood C n U, isOpen_stepNeighborhood C n hU, ?_,
    stepNeighborhoodInclusion C n U hU, stepNeighborhoodRetraction C n U hU,
    fun _ ↦ rfl, stepNeighborhoodRetraction_old C n U hU,
    stepNeighborhoodDeformation C n U hU, stepNeighborhoodDeformation_fixed C n U hU⟩
  ext x
  exact skeletonInclusion_mem_stepNeighborhood C n U x

end Consumer.CWSkeletonNeighborhood
