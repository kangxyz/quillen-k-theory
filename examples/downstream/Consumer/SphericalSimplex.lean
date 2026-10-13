/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.SphericalSimplexParametrization

/-! # Independent detection of the original cubical unit by a singular-simplex nullhomotopy -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Quillen Convexity
open scoped Topology unitInterval
universe u

namespace Consumer.SphericalSimplex
variable {Z : Type u} [TopologicalSpace Z] {z : Z} {n : ℕ}

/-- A nullhomotopy of every actual spherical simplex kills the existing cubical group.
This tests the orientation-free representation interface needed by first-obstruction detection. -/
theorem homotopyGroup_subsingleton_of_spherical_nullhomotopies
    (h : ∀ f : SphericalSimplex Z z (n + 1),
      f.val.HomotopicRel (ContinuousMap.const _ z) (simplexBoundary (n + 1))) :
    Subsingleton (HomotopyGroup.Pi (n + 1) Z z) := by
  have hall (a : HomotopyGroup.Pi (n + 1) Z z) : a = 1 := by
    obtain ⟨f, rfl⟩ := SphericalSimplex.homotopyClass_surjective a
    exact f.homotopyClass_eq_one_iff.mpr (h f)
  exact ⟨fun a b ↦ (hall a).trans (hall b).symm⟩

/-- The downstream criterion concerns the original cube and its actual relative homotopies. -/
theorem original_cube_null_iff (p : GenLoop (Fin (n + 1)) Z z) :
    (Quotient.mk' p : HomotopyGroup.Pi (n + 1) Z z) =
      (1 : HomotopyGroup.Pi (n + 1) Z z) ↔
      (SphericalSimplex.ofGenLoop p).val.HomotopicRel (ContinuousMap.const _ z)
        (simplexBoundary (n + 1)) := by
  constructor
  · intro h
    exact (SphericalSimplex.homotopyClass_eq_one_iff _).mp
      ((SphericalSimplex.homotopyClass_ofGenLoop p).trans h)
  · intro h
    exact (SphericalSimplex.homotopyClass_ofGenLoop p).symm.trans
      ((SphericalSimplex.homotopyClass_eq_one_iff _).mpr h)

/-- Vanishing established with an explicitly controlled parametrization kills the original Pi. -/
theorem homotopyGroup_subsingleton_of_specified_classes
    (e : (Fin (n + 1) → I) ≃ₜ StdSimplex ℝ (Fin (n + 2)))
    (he : ∀ t, e t ∈ simplexBoundary (n + 1) ↔ t ∈ _root_.Cube.boundary (Fin (n + 1)))
    (h : ∀ f : SphericalSimplex Z z (n + 1), SphericalSimplex.homotopyClassWith e he f = 1) :
    Subsingleton (HomotopyGroup.Pi (n + 1) Z z) := by
  apply homotopyGroup_subsingleton_of_spherical_nullhomotopies
  intro f
  exact (SphericalSimplex.homotopyClassWith_eq_one_iff e he f).mp (h f)

end Consumer.SphericalSimplex
