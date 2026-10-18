/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.H2CapDescent
public import Quillen.Topology.HomotopyGroups.Connectivity.SimplyConnected
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfectness of the original fiber group for an injective H-two surjection

The chain argument puts the original connecting image in the commutator.
The actual fiber exact sequence then has surjective projection to the perfect
source group, with kernel contained in the commutator. The elementary group
argument below proves perfectness of the original fiber group.
-/

@[expose] public section
noncomputable section
universe u v
namespace Quillen.HomotopyFiber

/-- A surjection to a perfect group with kernel in the commutator has perfect source. -/
theorem isPerfect_of_surjective_of_ker_le_commutator
    {H : Type u} {G : Type v} [Group H] [Group G] [Group.IsPerfect G]
    (p : H →* G) (hp : Function.Surjective p) (hk : p.ker ≤ commutator H) :
    Group.IsPerfect H := by
  have hc : (commutator H).map p = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective p hp]
    exact Group.IsPerfect.commutator_eq_top
  refine ⟨top_unique ?_⟩
  intro a _
  have ha : p a ∈ (commutator H).map p := by rw [hc]; trivial
  obtain ⟨c, hc, he⟩ := ha
  have hk' : a * c⁻¹ ∈ commutator H := hk (by
    change p (a * c⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel])
  simpa only [inv_mul_cancel_right] using (commutator H).mul_mem hk' hc

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [PathConnectedSpace X] [SimplyConnectedSpace Y]

/-- The actual fiber of an injective integral H-two surjection has perfect Pi one
when the original source Pi one is perfect. -/
theorem piOne_isPerfect_of_injective_of_h2_surjective
    (j : C(X, Y)) (hj : Function.Injective j) (x : X)
    [Group.IsPerfect (HomotopyGroup.Pi 1 X x)]
    (hH : Function.Surjective (LocalCoefficients.pushforwardHomologyMap j
      (LocalCoefficients.constant Y LocalCoefficients.integralCoefficientModule.{u}) 2)) :
    Group.IsPerfect (HomotopyGroup.Pi 1 (HomotopyFiber j (j x))
      (basepoint j (j x) x rfl)) := by
  let p := piMap 0 (projection j (j x)) (projection_basepoint j (j x) x rfl)
  have hp : Function.Surjective p := by
    apply MonoidHom.range_eq_top.mp
    change (piMap 0 (projection j (j x)) (projection_basepoint j (j x) x rfl)).range = ⊤
    rw [piMap_range_projection_eq_ker]
    let := subsingleton_homotopyGroup_one_of_simplyConnected (j x)
    ext a
    simp only [MonoidHom.mem_ker, Subgroup.mem_top, iff_true]
    exact Subsingleton.elim _ _
  have hk : p.ker ≤ commutator _ := by
    rw [show p = piMap 0 (projection j (j x))
      (projection_basepoint j (j x) x rfl) from rfl,
      ← range_connectingHom_eq_ker_projection]
    exact LocalCoefficients.range_connectingHom_le_commutator_of_h2_surjective j hj x hH
  exact isPerfect_of_surjective_of_ker_le_commutator p hp hk

end Quillen.HomotopyFiber
