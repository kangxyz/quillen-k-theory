/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.WeakImageCofinality

/-! # Original cofinality maps with genuinely independent category universes -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Tests.GeneralCofinality
open Waldhausen Cofinality Fibration
section Transport
variable {C G : Type u} [Category.{v} C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

/-- Universe transport retains the exact value of the original lowered object. -/
theorem original_grade_value (A : SmallModel C) :
    (d.smallModelGrading.value A).down = d.value (AsSmall.down.obj A) := rfl

/-- Lifted coarse arrows are exactly the original down-mapped coarse arrows. -/
theorem original_coarse_arrow {A B : SmallModel C} (f : A ⟶ B) :
    d.smallModelGrading.coarseStructure.weq f ↔ d.coarseStructure.weq (AsSmall.down.map f) :=
  ULift.ext_iff
end Transport

section LargerObjects
variable {C : Type (u + 1)} [Category.{u} C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)
include D hs

/-- Scheme-sized object universes retain injectivity of the literal original K-zero inclusion. -/
theorem original_KZero_injective_large_objects {a b : h.waldhausenStructure.K 0}
    (he : KMap h.inclusion_exact 0 a = KMap h.inclusion_exact 0 b) : a = b :=
  h.inclusion_KMap_injective_general D hs 0 he
end LargerObjects

section LargerHoms
variable {C : Type u} [Category.{u + 1} C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)
include D hs

/-- The reverse universe inequality also retains unique original positive-K preimages. -/
theorem original_positive_preimage_large_homs (n : ℕ) (b : W.K (n + 1)) :
    ∃! a, KMap h.inclusion_exact (n + 1) a = b :=
  (h.inclusion_KMap_succ_bijective_general D hs n).existsUnique b
end LargerHoms

section OriginalFunctor
open ApproximationImage
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationOnImage W V F) (hF : IsExact W.cof W.weq V.cof V.weq F)
  [HasBinaryCoproducts D] (H : DenseCofiberData V (objects V F)) [V.weq.HasTwoOutOfThreeProperty]
  (J : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (D' : RowFactorization.JointData (NestedWeakEquivalences.refl V))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl V) D')
include h H J D' hs

/-- Approximation onto the actual image and its genuine density give original-map preimages. -/
theorem original_functor_positive_preimage (n : ℕ) (b : V.K (n + 1)) :
    ∃! a, KMap hF (n + 1) a = b := (original_KMap_succ_bijective_of_dense h hF H J D' hs n).existsUnique b

/-- The original functor has precisely the genuine remaining K-zero kernel as its image. -/
theorem original_functor_KZero_lifts_iff (b : V.K 0) :
    (∃ a, KMap hF 0 a = b) ↔ KMap (changeWeak_exact H.grading.nested) 0 b = 1 := by
  change b ∈ (KMap hF 0).range ↔ _
  rw [original_range_KMap_of_dense h hF H J D' hs 0]
  rfl
end OriginalFunctor
end Quillen.Tests.GeneralCofinality
