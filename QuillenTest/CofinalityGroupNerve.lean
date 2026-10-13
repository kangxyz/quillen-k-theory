/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Cofinality.GradedGroupRealization

/-! # Actual range, finite realization, and original group-grading map consumers -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v w
namespace QuillenTest.CofinalityGroupNerve

open Quillen
open Waldhausen Cofinality
section Range
variable {C : Type u} [Category.{v} C] {G : Type w} [AddCommGroup G]
  {W : Structure C} (d : Grading W G) (T : FunctorialFactorization W)

include T in
/-- Every negative grade still has an actual original object, with independent universes. -/
theorem actual_negative_representative (A : C) : ∃ Q : C, d.value Q = -d.value A :=
  d.exists_value_neg T A

/-- No new elements are added when the actual object range becomes a group. -/
theorem range_membership_original_object (g : G) :
    g ∈ d.valueRange T ↔ ∃ A : C, d.value A = g := Iff.rfl

/-- Codrestricting grades preserves the original coarse weakness of every original arrow. -/
theorem original_coarse_arrow_unchanged {A B : C} (f : A ⟶ B) :
    (d.rangeGrading T).coarseStructure.weq f ↔ d.coarseStructure.weq f :=
  d.rangeGrading_weak_iff T f
end Range

section GroupNerve
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G) (T : FunctorialFactorization W)

/-- Arbitrary finite actual-range values are realized by a genuine original quotient row. -/
theorem actual_finite_range_realization (n : SimplexCategory)
    (a : Fin (n.len + 1) → d.valueRange T) :
    ∃ R : QuotientRows.Obj (d.rangeGrading T).coarseStructure n,
      (d.rangeGrading T).rowValue n R = fun p ↦ a p.val.2 - a p.val.1 :=
  (d.rangeGrading T).exists_rowValue_difference T (d.valueToRange_surjective T) n a

/-- Every original group arrow is recovered exactly from its actual quotient-row representative. -/
theorem actual_nerve_arrow_recovered (n : SimplexCategory)
    (F : ComposableArrows (SingleObj (Multiplicative (d.valueRange T))) n.len)
    (p : Interval n) :
    ((d.rangeGrading T).rowGradeChain n
      ((d.rangeGrading T).chainRowGrade T (d.valueToRange_surjective T) F)).map
        (homOfLE p.property) = F.map (homOfLE p.property) := rfl

/-- Arbitrary ordinal restriction keeps precisely the original first-row grid coordinates. -/
theorem original_group_grade_restriction {m n : SimplexCategory} (α : m ⟶ n)
    (X : (sSet d.coarseStructure.cof d.coarseStructure.weq).obj (op n)) (p : Interval m) :
    ((@Multiplicative.toAdd (d.valueRange T)
      (((nerve (SingleObj (Multiplicative (d.valueRange T)))).map α.op
        ((d.groupGradeMap T).app (op n) X)).map (homOfLE p.property))) : G) =
      d.value (X.val.obj (0, (QuotientRows.indexMap α).obj p)) := rfl

/-- Complete weakness includes every original based homotopy comparison, including dimension zero.
  -/
theorem original_group_grade_homotopy (x : d.coarseStructure.Delooping) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (SSet.toTop.map (d.groupGradeMap T)).hom (x := x) rfl) :=
  (d.groupGradeMap_isRealizationWeakEquivalence T).homotopy_bijective x n

/-- Every actual point of the group nerve realization is reached up to an actual path. -/
theorem original_group_grade_component
    (y : SSet.toTop.obj (nerve (SingleObj (Multiplicative (d.valueRange T))))) :
    ∃ x, Joined ((SSet.toTop.map (d.groupGradeMap T)) x) y :=
  (d.groupGradeMap_isRealizationWeakEquivalence T).component_surjective y

/-- Passing to the exact subgroup and back preserves all original row grades literally. -/
theorem original_row_range_roundtrip (n : SimplexCategory) (a : d.RowGrade n) :
    d.rowGradeFromRange T n (d.rowGradeToRange T n a) = a := rfl
end GroupNerve
end QuillenTest.CofinalityGroupNerve
