/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.CubicalBoundaryInduction

/-! A downstream signed integer-coefficient consumer of genuine cubical addition. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u

namespace Quillen.Consumer.CubicalBoundaryInduction

/-- An arbitrary signed integer coefficient multiplies the genuine original
cubical boundary relation; no simplex comparison or Hurewicz premise is used. -/
theorem signed_coefficient_cubical_boundary {Z : Type u} [TopologicalSpace Z]
    {z : Z} {m : ℕ} (F : C((Fin (m + 3) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), F x = z) (a : ℤ) :
    ∑ j : Fin (m + 3), ((-1 : ℤ) ^ j.val) •
      (a • (Additive.ofMul (cubicalClass
          (cubicalSphericalFace F hF j 1 (Or.inr rfl))) -
        Additive.ofMul (cubicalClass
          (cubicalSphericalFace F hF j 0 (Or.inl rfl))))) =
        (0 : Additive (HomotopyGroup.Pi (m + 2) Z z)) := by
  let v (j : Fin (m + 3)) : Additive (HomotopyGroup.Pi (m + 2) Z z) :=
    Additive.ofMul (cubicalClass (cubicalSphericalFace F hF j 1 (Or.inr rfl))) -
      Additive.ofMul (cubicalClass (cubicalSphericalFace F hF j 0 (Or.inl rfl)))
  change ∑ j : Fin (m + 3), ((-1 : ℤ) ^ j.val) • (a • v j) = 0
  have h : ∑ j : Fin (m + 3), ((-1 : ℤ) ^ j.val) • v j = 0 :=
    cubical_signed_boundary_addition F hF
  calc
    _ = a • ∑ j : Fin (m + 3), ((-1 : ℤ) ^ j.val) • v j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun j _ ↦ smul_comm _ _ _)
    _ = 0 := by rw [h, smul_zero]

end Quillen.Consumer.CubicalBoundaryInduction
