/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Cofinality.DenseKEquivalence

/-! # Genuine complement density and literal original full-inclusion consumers -/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace QuillenTest.DenseSubcategoryCofinality

open Quillen
open Waldhausen Cofinality Fibration
section Categorical
variable {C : Type u} [Category.{v} C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)
include h

/-- Equality of actual classes retains a common original categorical complement. -/
theorem equality_has_actual_complement (A B : C) (he : h.classOf A = h.classOf B) :
    ∃ Z : C, P (A ⨿ Z) ∧ P (B ⨿ Z) := (h.classOf_eq_iff A B).mp he

/-- Original weak arrows preserve the actual common-complement class. -/
theorem original_weak_class {A B : C} (f : A ⟶ B) (hf : W.weq f) :
    h.grading.value A = h.grading.value B := h.classOf_weak f hf

/-- An actual cofiber sequence has a genuine common complement with its source-plus-quotient. -/
theorem original_cofiber_complement {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (hQ : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    ∃ Z : C, P (B ⨿ Z) ∧ P ((A ⨿ Q) ⨿ Z) := h.related_cofiber hi hQ

/-- The constructed grading recognizes precisely the original full-subcategory membership. -/
theorem exact_original_membership (A : C) : h.grading.value A = 0 ↔ P A := h.grading_zero_iff A

/-- The inherited zero-grade comparison keeps every original ambient arrow literally. -/
theorem original_comparison_arrow {A B : P.FullSubcategory} (f : A ⟶ B) :
    (h.toZeroGrade.map f).hom = f.hom := rfl

/-- Closure of an arbitrary displayed ambient pushout follows from the original structural data. -/
theorem original_ambient_pushout_closed {A B D Q : C} {i : A ⟶ B} {f : A ⟶ D}
    {g : B ⟶ Q} {j : D ⟶ Q} (hi : W.cof i) (hQ : IsPushout i f g j)
    (hA : P A) (hB : P B) (hD : P D) : P Q := h.closed.pushout_mem hi hQ hA hB hD
end Categorical

section Groups
variable {C : Type u} [SmallCategory C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)
include D hs

/-- Positive K-classes have unique preimages under the unchanged original full inclusion. -/
theorem unique_original_positive_preimage (n : ℕ) (b : W.K (n + 1)) :
    ∃! a, KMap h.inclusion_exact (n + 1) a = b :=
  (h.inclusion_KMap_succ_bijective D hs n).existsUnique b

/-- The actual K-zero inclusion is injective without a grading or cofinality endpoint premise. -/
theorem original_KZero_injective {a b : h.waldhausenStructure.K 0}
    (he : KMap h.inclusion_exact 0 a = KMap h.inclusion_exact 0 b) : a = b :=
  h.inclusion_KMap_injective D hs 0 he

/-- Degree-zero lifting holds exactly on the true remaining kernel, retaining the original map. -/
theorem original_KZero_lifts_iff (b : W.K 0) :
    (∃ a, KMap h.inclusion_exact 0 a = b) ↔ KMap (changeWeak_exact h.grading.nested) 0 b = 1 := by
  change b ∈ (KMap h.inclusion_exact 0).range ↔ _
  rw [h.range_inclusion_KMap D hs 0]
  rfl
end Groups
end QuillenTest.DenseSubcategoryCofinality
