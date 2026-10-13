/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.CubicalBoundaryInduction

/-! Concrete map, dimension-two orientation, and terminal-homotopy regression tests. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u

namespace QuillenTest.CubicalBoundaryInduction

open Quillen
variable {Z : Type u} [TopologicalSpace Z] {z : Z}

/-- The degree-two relation contains all six original square faces, with the
three coordinate signs positive, negative, positive. -/
theorem dimensionTwo_six_faces (F : C((Fin 3 → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin 3), F x = z) :
    (Additive.ofMul (cubicalClass (cubicalSphericalFace F hF 0 1 (Or.inr rfl))) -
      Additive.ofMul (cubicalClass (cubicalSphericalFace F hF 0 0 (Or.inl rfl)))) -
    (Additive.ofMul (cubicalClass (cubicalSphericalFace F hF 1 1 (Or.inr rfl))) -
      Additive.ofMul (cubicalClass (cubicalSphericalFace F hF 1 0 (Or.inl rfl)))) +
    (Additive.ofMul (cubicalClass (cubicalSphericalFace F hF 2 1 (Or.inr rfl))) -
      Additive.ofMul (cubicalClass (cubicalSphericalFace F hF 2 0 (Or.inl rfl)))) =
      (0 : Additive (HomotopyGroup.Pi 2 Z z)) := by
  have h := cubical_signed_boundary_addition (m := 0) F hF
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_succ, one_mul, neg_one_mul, neg_neg, one_smul, neg_smul, add_zero,
    sub_eq_add_neg, neg_add_rev, add_assoc,
    show (Fin.succ (0 : Fin 2) : Fin 3) = 1 from rfl,
    show (Fin.succ (Fin.succ (0 : Fin 1)) : Fin 3) = 2 from rfl] using h

/-- The reparametrization in lateral slot one is literally coordinate exchange,
so it has negative class sign, rather than an assumed orientation convention. -/
theorem second_lateral_class_negative (F : C((Fin 3 → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin 3), F x = z) :
    Additive.ofMul (cubicalClass (lateralGenLoop F hF (1 : Fin 2) 0 (Or.inl rfl))) =
      -Additive.ofMul (cubicalClass
        (cubicalSphericalFace F hF (2 : Fin 3) 0 (Or.inl rfl))) := by
  simpa using lateralGenLoop_additiveClass F hF (1 : Fin 2) 0 (Or.inl rfl)

/-- The first finite step really kills both original sides, pointwise on the
whole face, including points away from the face boundary. -/
theorem first_pair_is_pointwise_constant (F : C((Fin 3 → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin 3), F x = z) :
    ∃ (G : C((Fin 3 → I), Z)), ∀ x,
      x (1 : Fin 3) = 0 ∨ x (1 : Fin 3) = 1 → G x = z := by
  let P := (CubicalKillState.initial F hF).insert (0 : Fin 2) (by simp)
  exact ⟨P.cube, fun x hx ↦ P.killed 0 (by simp) x hx⟩

/-- Full side killing retains a genuine relative homotopy on actual maps,
whose initial map is the original bottom loop. -/
theorem full_killing_gives_actual_homotopy {m : ℕ}
    (F : C((Fin (m + 3) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), F x = z) :
    ∃ (G : C((Fin (m + 3) → I), Z))
      (hG : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), G x = z),
      Nonempty ((bottomGenLoop F hF).val.HomotopyRel (topGenLoop G hG).val
        (Cube.boundary (Fin (m + 2)))) := by
  obtain ⟨P⟩ := exists_cubicalKillState F hF Finset.univ
  refine ⟨P.cube, P.based, ?_⟩
  have H := allSidesConstantHomotopy P.cube P.based
    (fun k x hx ↦ P.killed k (Finset.mem_univ k) x hx)
  rw [P.bottom] at H
  exact ⟨H⟩

end QuillenTest.CubicalBoundaryInduction
