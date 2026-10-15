/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionJointData

/-! Original joint arrows and the unchanged positive graded K-groups remain directly usable. -/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace QuillenTest.FullOpenSectionJointData

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The transported joint retains the exact original arrow factorization. -/
theorem original_joint_factorization (a : Under R)
    (f : Arrow (BoundedFlatAffineFullOpenSections j a)) :
    (boundedFlatAffineFullOpenSectionJointData j a).inl.app f ≫
        ((boundedFlatAffineFullOpenSectionJointData j a).joint.obj f).obj.hom ≫
        (boundedFlatAffineFullOpenSectionJointData j a).projection.app f = f.hom :=
  (boundedFlatAffineFullOpenSectionJointData j a).factorization f

/-- Positive vanishing concerns the original graded structure, without replacing its group. -/
theorem original_positive_group (a : Under R) (n : ℕ) :
    Subsingleton ((boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.K (n + 1)) :=
  boundedFlatAffineFullOpenGradedSection_K_succ_subsingleton j a n

/-- Every original positive class equals the identity in that same K-group. -/
theorem original_positive_class_eq_one (a : Under R) (n : ℕ)
    (x : (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.K (n + 1)) : x = 1 := by
  let := boundedFlatAffineFullOpenGradedSection_K_succ_subsingleton j a n
  exact Subsingleton.elim _ _

end QuillenTest.FullOpenSectionJointData
