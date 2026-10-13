/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.ClassifyingSpace.IteratedFirstTransitions
public import Quillen.Topology.ClassifyingSpace.Equivalence
public import Quillen.CategoryTheory.TheoremB.FullWeakComparison

/-! # Weak idempotence of actual action localization -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace Quillen.GroupCompletion.Localization
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [MonoidalCategory C] [SymmetricCategory C] [IsGroupoid C]
  [∀ A : C, (tensorRight A).Faithful] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

/-- The canonical localization entry uses the unit in the new first coordinate. -/
def iteratedUnitEntry : Localization C D ⥤ Localization C (Localization C D) :=
  commaEntry (D := Localization C D) (𝟙_ C) ⋙ CostructuredArrow.proj projection ⟨𝟙_ C⟩

omit [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful] in
@[simp]
lemma iteratedUnitEntry_obj (X : Localization C D) :
    iteratedUnitEntry.obj X = (⟨(𝟙_ C, X)⟩ : Localization C (Localization C D)) := rfl

/-- The iterated first projection satisfies the original weak transition condition. -/
theorem iteratedFirstTransitionWeakEquivalences :
    TheoremB.TransitionWeakEquivalences (projection (C := C) (D := Localization C D)) := by
  intro A B f
  obtain ⟨e, he⟩ := exists_iteratedFirstTransitionHomotopyEquiv (D := D) f
  have h := isWeakHomotopyEquivalence_of_homotopyEquiv e
  rw [he, classifyingSpaceMapUniversal_eq] at h
  exact h

/-- Localizing an already localized category preserves its actual classifying
space up to weak equivalence, by the canonical unit entry. -/
theorem iteratedUnitEntry_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (classifyingSpaceMap (iteratedUnitEntry (C := C) (D := D))).hom := by
  have hp := TheoremB.commaProjection_isWeakHomotopyEquivalence_of_contraction
    (projection (C := C) (D := Localization C D)) iteratedFirstTransitionWeakEquivalences
    (⟨𝟙_ C⟩ : ActionLocalization C C)
    (classifyingSpaceInitialContraction (ActionLocalization.selfUnitIsInitial (C := C))).symm
  have he := isWeakHomotopyEquivalence_of_homotopyEquiv
    (commaEntryClassifyingHomotopyEquiv (D := Localization C D) (𝟙_ C))
  rw [commaEntryClassifyingHomotopyEquiv_toFun, classifyingSpaceMapUniversal_eq] at he
  simpa only [iteratedUnitEntry, classifyingSpaceMap_comp, TopCat.hom_comp] using hp.comp he

end Quillen.GroupCompletion.Localization
