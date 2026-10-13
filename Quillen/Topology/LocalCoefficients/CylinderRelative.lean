/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.CylinderHomology
public import Quillen.Topology.LocalCoefficients.RelativeHomotopyEquivalence

/-! # Relative vanishing for actual closed cylinder slices -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped unitInterval
universe u
namespace Quillen.LocalCoefficients
variable (X : Type u) [TopologicalSpace X]

/-- A genuine closed slice of the interval cylinder. -/
def cylinderSlice (t : unitInterval) : Set (unitInterval × X) := {z | z.1 = t}

/-- The actual slice is homeomorphic to the original space via its second projection. -/
def cylinderSliceHomeomorph (t : unitInterval) : cylinderSlice X t ≃ₜ X where
  toFun z := z.val.2
  invFun x := ⟨(t, x), rfl⟩
  left_inv z := by apply Subtype.ext; exact Prod.ext z.property.symm rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The homotopy equivalence whose forward map is exactly the subspace inclusion. -/
def cylinderSliceInclusionEquiv (t : unitInterval) :
    ContinuousMap.HomotopyEquiv (cylinderSlice X t) (unitInterval × X) :=
  (cylinderSliceHomeomorph X t).toHomotopyEquiv.trans (cylinderProjectionEquiv X t).symm

/-- The composite equivalence retains the original inclusion on every point. -/
theorem cylinderSliceInclusionEquiv_toFun (t : unitInterval) :
    (cylinderSliceInclusionEquiv X t).toFun = subspaceInclusion (cylinderSlice X t) := by
  apply ContinuousMap.ext
  intro z
  change (t, z.val.2) = z.val
  exact Prod.ext z.property.symm rfl

/-- The genuine cylinder/slice relative complex is acyclic for every cylinder local system. -/
theorem cylinderSlice_relative_acyclic (t : unitInterval)
    (A : System.{u, u} (unitInterval × X)) :
    (relativeSingularChainComplex (cylinderSlice X t) A).Acyclic :=
  relativeSingularChainComplex_acyclic_of_homotopyEquiv _ A
    (cylinderSliceInclusionEquiv X t) (cylinderSliceInclusionEquiv_toFun X t)

end Quillen.LocalCoefficients
