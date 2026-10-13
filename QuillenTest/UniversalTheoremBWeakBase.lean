/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.CategoryTheory.TheoremB.UniverseWeakComparison

/-! Regression tests for actual comma projections in independent category universes. -/
noncomputable section
open CategoryTheory Quillen
universe u₁ v₁ u₂ v₂ w

example {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D)
    (h : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (CostructuredArrow.map (S := F) f)))
    (d : D)
    (hD : IsWeakHomotopyEquivalence (ContinuousMap.const (ClassifyingSpace D)
      (PUnit.unit : PUnit.{w + 1}))) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (CostructuredArrow.proj F d)) :=
  TheoremB.commaProjectionUniversal_isWeakHomotopyEquivalence_of_weakBase F h d hD

example {C : Type u₁} [Category.{v₁} C] {D : Type (u₁ + 1)} [Category.{v₁ + 1} D]
    (F : C ⥤ D) (h : TheoremB.TransitionWeakEquivalencesUniversal F) (d : D)
    (hD : IsWeakHomotopyEquivalence (ContinuousMap.const (ClassifyingSpace D) PUnit.unit))
    (x : ClassifyingSpace C) :
    ∃ y : ClassifyingSpace (CostructuredArrow F d),
      Joined (classifyingSpaceMapUniversal (CostructuredArrow.proj F d) y) x :=
  (TheoremB.commaProjectionUniversal_isWeakHomotopyEquivalence_of_weakBase
    F h d hD).component_surjective x

example {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (h : TheoremB.TransitionWeakEquivalencesUniversal F) (d : D)
    (hD : IsWeakHomotopyEquivalence (ContinuousMap.const (ClassifyingSpace D)
      (PUnit.unit : PUnit.{w + 1})))
    (x : ClassifyingSpace (CostructuredArrow F d)) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (classifyingSpaceMapUniversal (CostructuredArrow.proj F d)) (x := x) rfl) :=
  (TheoremB.commaProjectionUniversal_isWeakHomotopyEquivalence_of_weakBase
    F h d hD).homotopy_bijective x n

example {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) (x : CostructuredArrow F d) :
    classifyingSpaceMapUniversal (CostructuredArrow.proj F d) (classifyingSpacePoint x) =
      classifyingSpacePoint x.left :=
  classifyingSpaceMapUniversal_point (CostructuredArrow.proj F d) x
