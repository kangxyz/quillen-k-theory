/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.SphericalSimplexParametrization

/-! # Genuine spherical-simplex representatives and relative homotopy tracks -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Quillen Convexity
open scoped Topology unitInterval
universe u

namespace QuillenTest.SphericalSimplex
variable {Z : Type u} [TopologicalSpace Z] {z : Z}

/-- The zero-dimensional edge case uses the same actual pair homeomorphism. -/
theorem degree_zero_representative (a : HomotopyGroup.Pi 0 Z z) :
    ∃ f : SphericalSimplex Z z 0, f.homotopyClass = a :=
  SphericalSimplex.homotopyClass_surjective a

/-- Empty boundary in degree zero permits every point, independently of the named basepoint. -/
theorem degree_zero_arbitrary_point (w : Z) :
    ∃ f : SphericalSimplex Z z 0, ∀ x, f x = w := by
  refine ⟨⟨ContinuousMap.const _ w, ?_⟩, fun _ ↦ rfl⟩
  intro x hx
  have ht : (Cube.simplexHomeomorph 0).symm x ∈ _root_.Cube.boundary (Fin 0) := by
    rw [← Cube.simplexHomeomorph_mem_boundary_iff]
    simpa using hx
  obtain ⟨i, _⟩ := ht
  exact Fin.elim0 i

/-- A degree-two representative retains the original cubical map pointwise. -/
theorem degree_two_original_cube (p : GenLoop (Fin 2) Z z) (t : Fin 2 → I) :
    (SphericalSimplex.ofGenLoop p).toGenLoop t = p t := by simp

/-- Degree two already lands in the original commutative homotopy group. -/
theorem degree_two_add_comm (f g : SphericalSimplex Z z 2) :
    f.additiveClass + g.additiveClass = g.additiveClass + f.additiveClass := add_comm _ _

/-- Conversion carries the actual relative homotopy, not only its endpoint classes. -/
theorem degree_two_homotopy_track {f g : SphericalSimplex Z z 2}
    (H : f.val.HomotopyRel g.val (simplexBoundary 2)) (s : I) (t : Fin 2 → I) :
    SphericalSimplex.homotopyToGenLoop H (s, t) = H (s, Cube.simplexHomeomorph 2 t) := rfl

/-- Both conversions recover every point on every time slice of the original homotopy. -/
theorem degree_two_homotopy_round_trip {f g : SphericalSimplex Z z 2}
    (H : f.val.HomotopyRel g.val (simplexBoundary 2)) (s : I)
    (x : StdSimplex ℝ (Fin 3)) :
    SphericalSimplex.homotopyFromGenLoop (SphericalSimplex.homotopyToGenLoop H) (s, x) =
      H (s, x) := by simp

/-- Vanishing of the original class yields an actual boundary-fixed simplex nullhomotopy. -/
theorem degree_two_nullhomotopy (f : SphericalSimplex Z z 2) (h : f.homotopyClass = 1) :
    Nonempty (f.val.HomotopyRel (ContinuousMap.const _ z) (simplexBoundary 2)) :=
  f.homotopyClass_eq_one_iff.mp h

/-- The constant simplex is the group unit, including the noncommutative degree-one range. -/
theorem degree_one_constant :
    (SphericalSimplex.const : SphericalSimplex Z z 1).homotopyClass = 1 := by simp

/-- A future controlled pair can replace the existential choice for vanishing detection. -/
theorem degree_two_specified_pair_vanishing
    (e : (Fin 2 → I) ≃ₜ StdSimplex ℝ (Fin 3))
    (he : ∀ t, e t ∈ simplexBoundary 2 ↔ t ∈ _root_.Cube.boundary (Fin 2))
    (f : SphericalSimplex Z z 2) :
    SphericalSimplex.homotopyClassWith e he f = 1 ↔ f.homotopyClass = 1 := by
  rw [SphericalSimplex.homotopyClassWith_eq_one_iff, SphericalSimplex.homotopyClass_eq_one_iff]

end QuillenTest.SphericalSimplex
