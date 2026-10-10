/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Cofinality.GradedRealization

/-! # Actual coarse grading and original S-map consumers -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v w
namespace Quillen.Tests.CofinalityGrading
open Waldhausen Cofinality
section Categorical
variable {C : Type u} [Category.{v} C] {G : Type w} [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

/-- Changing weak equivalences leaves the entire original cofibration class and zero unchanged. -/
theorem unchanged_original_data : d.coarseStructure.cof = W.cof ∧ d.coarseStructure.zero = W.zero :=
  ⟨rfl, rfl⟩

/-- Every actual original weak arrow remains weak in the genuine coarse structure. -/
theorem original_weak_remains_weak {A B : C} (f : A ⟶ B) (hf : W.weq f) :
    d.coarseStructure.weq f := d.nested.le_weq f hf

/-- Actual cofibration weakness is detected by the grade of its displayed original cofiber. -/
theorem actual_cofiber_zero_iff {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q} (hi : W.cof i)
    (hQ : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    d.coarseStructure.weq i ↔ d.value Q = 0 := by
  change d.value A = d.value B ↔ _
  rw [d.cofiber_value hi hQ, sub_eq_zero]
  exact eq_comm

/-- The actual fibration kernel excludes objects whose original grade does not vanish. -/
theorem nonzero_grade_not_acyclic (A : C) (hA : d.value A ≠ 0) :
    ¬ Fibration.acyclicObjects d.nested A := fun h ↦ hA ((d.acyclicObjects_iff A).mp h)
end Categorical

section Realization
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

/-- Every point of the discrete row target carries an original actual quotient row. -/
theorem actual_grade_representative (n : SimplexCategory) (a : d.RowGrade n) :
    ∃ X : QuotientRows.Obj d.coarseStructure n, ∀ p, d.value (X.obj.obj p) = a.val p := by
  obtain ⟨X, hX⟩ := a.property
  exact ⟨X, fun p ↦ congrFun hX p⟩

/-- The original row realization point map is exactly the forward comparison. -/
theorem original_row_vertex (n : SimplexCategory) (X : QuotientRows.WeakRows d.coarseStructure n) :
    d.rowProjectionHomotopyEquiv n (classifyingSpacePoint X) =
      classifyingSpacePoint (Discrete.mk (d.rowGrade n X.obj)) := by
  rw [d.rowProjectionHomotopyEquiv_toFun]
  exact classifyingSpaceMap_point (d.rowProjection n) X

/-- The unchanged original coarse grading map is bijective on all actual based homotopy groups. -/
theorem original_grading_homotopy_map (x : d.coarseStructure.Delooping) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (SSet.toTop.map d.gradeMap).hom (x := x) rfl)
      :=
  d.gradeMap_isRealizationWeakEquivalence.homotopy_bijective x n

/-- Complete weakness retains component surjectivity onto the actual grade realization. -/
theorem original_grading_component (y : SSet.toTop.obj d.gradeSSet) :
    ∃ x, Joined ((SSet.toTop.map d.gradeMap) x) y :=
  d.gradeMap_isRealizationWeakEquivalence.component_surjective y

/-- Restriction of the actual output grade retains the original grid coordinates. -/
theorem original_grade_restriction_coordinate {m n : SimplexCategory} (α : m ⟶ n)
    (X : (sSet d.coarseStructure.cof d.coarseStructure.weq).obj (op n)) (p : Interval m) :
    ((d.gradeSSet.map α.op (d.gradeMap.app (op n) X)).val p) =
      d.value (X.val.obj (0, (QuotientRows.indexMap α).obj p)) := rfl
end Realization
end Quillen.Tests.CofinalityGrading
