/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Cofinality.ZeroGrade

/-! # Original zero-grade inclusion and genuine K-zero endpoint consumers -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace Quillen.Tests.GradedCofinality
open Waldhausen Cofinality Fibration
section Cylinder
variable {C : Type u} [Category.{v} C] {G : Type w} [AddCommGroup G]
  {W : Structure C} (d : Grading W G)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))

/-- The actual source factorization preserves the entire original triangle strictly. -/
theorem original_factorization_triangle (f : Arrow C) :
    D.sourceFactorization.inclusion.app f ≫ D.projection.app f = f.hom :=
  D.sourceFactorization.factorization f

/-- Retargeting cylinder weakness changes neither endpoint nor the actual middle projection. -/
theorem original_graded_joint_maps (f : Arrow C) :
    (d.jointData D).inl.app f = D.inl.app f ∧
    (d.jointData D).inr.app f = D.inr.app f ∧
    (d.jointData D).projection.app f = D.projection.app f := ⟨rfl, rfl, rfl⟩
end Cylinder

section Groups
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)
include D hs

/-- Every positive original K-class has a unique original zero-grade preimage. -/
theorem unique_original_positive_preimage (n : ℕ) (b : W.K (n + 1)) :
    ∃! a, KMap (acyclicInclusion_exact d.nested) (n + 1) a = b :=
  (d.zeroGradeKEquiv D hs n).bijective.existsUnique b

/-- The actual degree-zero inclusion is injective from the original structural cylinder data. -/
theorem original_KZero_injective {a b : (acyclicStructure d.nested).K 0}
    (h : KMap (acyclicInclusion_exact d.nested) 0 a = KMap (acyclicInclusion_exact d.nested) 0 b) :
    a = b := d.zeroGrade_KMap_injective D hs 0 h

/-- An original K-zero class lifts exactly when its actual coarse image vanishes. -/
theorem original_KZero_lifts_iff (b : W.K 0) :
    (∃ a, KMap (acyclicInclusion_exact d.nested) 0 a = b) ↔
      KMap (changeWeak_exact d.nested) 0 b = 1 := by
  change b ∈ (KMap (acyclicInclusion_exact d.nested) 0).range ↔ _
  rw [(d.zeroGrade_KZero_exact D hs).2.1]
  rfl

/-- Every point of the genuine remaining K-zero endpoint comes from an original fine class. -/
theorem original_remaining_KZero_preimage (b : d.coarseStructure.K 0) :
    ∃ a, KMap (changeWeak_exact d.nested) 0 a = b := (d.zeroGrade_KZero_exact D hs).2.2 b
end Groups
end Quillen.Tests.GradedCofinality
