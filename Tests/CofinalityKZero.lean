/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Cofinality.DenseKZero

/-! # Actual coarse K-zero, original realized arrows and genuine dense-inclusion image consumers -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.Tests.CofinalityKZero
open Waldhausen Cofinality Fibration
section Grading
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G) (T : FunctorialFactorization W)

/-- The original continuous map sends the actual chosen zero point to the actual group vertex. -/
theorem original_group_grade_basepoint :
    (SSet.toTop.map (d.groupGradeMap T)).hom d.coarseStructure.kBasepoint =
      classifyingSpacePoint (SingleObj.star (Multiplicative (d.valueRange T))) :=
        d.groupGradeMap_basepoint T

/-- Each actual original realized-arrow loop has a unique original coarse K-zero preimage. -/
theorem unique_original_arrow_preimage (g : Multiplicative (d.valueRange T)) :
    ∃! a, d.coarseKZeroToGroupPi T a = HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (Path.Homotopic.Quotient.mk (classifyingSpacePath (SingleObj.toEnd (Multiplicative
        (d.valueRange T)) g))) :=
  (d.coarseKZeroToGroupPi_bijective T).existsUnique _

/-- The inverse endpoint equivalence gives the original realized-arrow class under the original map.
  -/
theorem inverse_recovers_original_arrow (g : Multiplicative (d.valueRange T)) :
    d.coarseKZeroToGroupPi T ((d.coarseKZeroEquiv T).symm g) =
      GroupoidClassifying.singleObjPiOneEquiv (Multiplicative (d.valueRange T)) g :=
  (MulEquiv.ofBijective (d.coarseKZeroToGroupPi T) (d.coarseKZeroToGroupPi_bijective
    T)).apply_symm_apply _

variable (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)
include hs

/-- The actual fine K-zero grade equation detects precisely the original zero-grade inclusion image.
  -/
theorem original_grade_KZero_lifts_iff (a : W.K 0) :
    (∃ b, KMap (acyclicInclusion_exact d.nested) 0 b = a) ↔ d.gradeKZeroMap D a = 1 := by
  change a ∈ (KMap (acyclicInclusion_exact d.nested) 0).range ↔ _
  rw [d.range_zeroGrade_KZero D hs]
  rfl
end Grading

section Dense
variable {C : Type u} [SmallCategory C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)
include hs

/-- Every original object's actual complement class is reached by a genuine fine K-zero class. -/
theorem original_object_class_preimage (A : C) :
    ∃ a, h.classKZeroMap D a = Multiplicative.ofAdd (h.classOf A) := h.classKZeroMap_surjective D hs
      _

/-- An original fine K-zero class lifts uniquely exactly when its actual complement class is zero.
  -/
theorem unique_original_dense_KZero_preimage (a : W.K 0) (ha : h.classKZeroMap D a = 1) :
    ∃! b, KMap h.inclusion_exact 0 b = a := by
  have hm : a ∈ (h.classKZeroMap D).ker := ha
  rw [← h.range_inclusion_KZero_eq_classKernel D hs] at hm
  obtain ⟨b, hb⟩ := hm
  exact ⟨b, hb, fun c hc ↦ h.inclusion_KMap_injective D hs 0 (hc.trans hb.symm)⟩
end Dense
end Quillen.Tests.CofinalityKZero
