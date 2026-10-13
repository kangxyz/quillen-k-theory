/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.SphericalHomotopyAddition

/-! Independent exact H5 consumer: its universal signed premise is now a theorem
of actual cubical homotopy groups, with no orientation witness to supply. -/

@[expose] public section
noncomputable section
open Convexity
universe u
namespace Quillen.Consumer.SphericalHomotopyAddition
variable {Z : Type u} [TopologicalSpace Z] {z : Z} {m : ℕ}

/-- This is the exact universal addition statement used by finite H5 evaluation. -/
theorem signed_relation_for_finite_evaluation
    (τ : C(StdSimplex ℝ (Fin (m + 4)), Z))
    (hτ : ∀ x ∈ simplexSkeleton (m + 2) (m + 3), τ x = z) :
    ∑ i : Fin (m + 4), ((-1 : ℤ) ^ i.val) •
      Additive.ofMul (sphericalFace τ hτ i).homotopyClassStick =
        (0 : Additive (HomotopyGroup.Pi (m + 2) Z z)) :=
  spherical_signed_homotopy_addition τ hτ

/-- The controlled conclusion implies nullity in H2's original chosen class
without asserting equality of the two oriented class maps. -/
theorem controlled_nullity_implies_chosen_nullity (f : SphericalSimplex Z z (m + 2))
    (hf : f.homotopyClassStick = 1) : f.homotopyClass = 1 :=
  f.homotopyClassStick_eq_one_iff_chosen.mp hf

end Quillen.Consumer.SphericalHomotopyAddition
