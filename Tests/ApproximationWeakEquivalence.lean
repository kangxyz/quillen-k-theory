/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.WeakEquivalence

/-! # Consumers of the original weak-category approximation map

The generic compact-source criterion keeps its independent source universe.
The concrete consumers retain the original comma category, original functor,
all homotopy degrees, component surjectivity and empty-source obstruction.
-/
noncomputable section
open CategoryTheory Quillen.Waldhausen
open Quillen.Waldhausen.HasApproximationProperty
open scoped Topology
universe u v
namespace Quillen.Tests.ApproximationWeakEquivalence

/-- Arbitrary compact source spaces need no triangulation or CW structure. -/
theorem independent_compact_source {C : Type u} [SmallCategory C]
    (h : ∀ (J : Type u) [PartialOrder J] [Finite J] (K : J ⥤ C),
      (classifyingSpaceMap K).hom.Nullhomotopic)
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (f : C(S, ClassifyingSpace C)) : f.Nullhomotopic :=
  classifyingSpace_compactMap_nullhomotopic_of_finitePoset h f

/-- The point-map conclusion includes actual nonemptiness. -/
theorem finite_posets_force_nonempty {C : Type u} [SmallCategory C]
    (h : ∀ (J : Type u) [PartialOrder J] [Finite J] (K : J ⥤ C),
      (classifyingSpaceMap K).hom.Nullhomotopic) : Nonempty (ClassifyingSpace C) := by
  obtain ⟨x, _⟩ :=
    (classifyingSpace_toPoint_isWeakHomotopyEquivalence_of_finitePoset h).component_surjective
      PUnit.unit
  exact ⟨x⟩

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty] (T : FunctorialFactorization W)

include h T in
/-- The actual weak comma has all compact maps nullhomotopic. -/
theorem original_comma_compact_maps (Y : WideSubcategory V.weq)
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (f : C(S, ClassifyingSpace (WeakComma hF Y))) : f.Nullhomotopic := by
  apply classifyingSpace_compactMap_nullhomotopic_of_finitePoset (f := f)
  intro J _ _ K
  exact finitePoset_weakComma_classifyingMap_nullhomotopic h hF T Y K

include h T in
/-- The original exact functor induces every homotopy bijection. -/
theorem original_homotopy_maps (x : ClassifyingSpace (WideSubcategory W.weq)) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (classifyingSpaceMap hF.weakFunctor).hom (x := x) rfl) :=
  (weakFunctor_classifyingSpaceMap_isWeakHomotopyEquivalence h hF T).homotopy_bijective x n

include h T in
/-- The zeroth map is explicitly included without a positive-degree premise. -/
theorem original_zeroth_map (x : ClassifyingSpace (WideSubcategory W.weq)) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (classifyingSpaceMap hF.weakFunctor).hom (x := x) rfl) :=
  original_homotopy_maps h hF T x 0

include h T in
/-- Every actual target component is met by the original map. -/
theorem original_component_surjectivity (y : ClassifyingSpace (WideSubcategory V.weq)) :
    ∃ x, Joined ((classifyingSpaceMap hF.weakFunctor).hom x) y :=
  (weakFunctor_classifyingSpaceMap_isWeakHomotopyEquivalence h hF T).component_surjective y

include h hF T in
/-- An empty source realization cannot meet these hypotheses with a target object. -/
theorem empty_source_obstruction [IsEmpty (ClassifyingSpace (WideSubcategory W.weq))]
    (Y : D) : False := by
  obtain ⟨x, _⟩ := original_component_surjectivity h hF T
    (classifyingSpacePoint (⟨Y⟩ : WideSubcategory V.weq))
  exact isEmptyElim x

end Quillen.Tests.ApproximationWeakEquivalence
