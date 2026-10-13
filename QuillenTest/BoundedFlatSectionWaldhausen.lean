/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionReindexExact

/-!
# Consumers of actual pointwise section Waldhausen structure

These consumers use the original morphism classes, genuinely constructed pushouts, exact
coefficient maps and both original functors of the evaluation equivalence.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.PerfectComplexes
universe u
namespace QuillenTest.BoundedFlatSectionWaldhausen

open Quillen

/-- The declared cofibrations retain every original coefficient fiber. -/
theorem every_original_cofibration (R : CommRingCat.{u})
    {s t : BoundedFlatAffineSections R} (a : s ⟶ t) :
    (boundedFlatAffineSectionWaldhausen R).cof a ↔
      ∀ j : Under R, (boundedFlatPerfectWaldhausen (Spec j.right)).cof
        ((boundedFlatAffineEvaluationAt R j).map a) :=
  boundedFlatAffineSectionWaldhausen_cof_iff R a

/-- The declared weak equivalences retain every original coefficient fiber. -/
theorem every_original_weak_equivalence (R : CommRingCat.{u})
    {s t : BoundedFlatAffineSections R} (a : s ⟶ t) :
    (boundedFlatAffineSectionWaldhausen R).weq a ↔
      ∀ j : Under R, (boundedFlatPerfectWaldhausen (Spec j.right)).weq
        ((boundedFlatAffineEvaluationAt R j).map a) :=
  boundedFlatAffineSectionWaldhausen_weq_iff R a

/-- Original pointwise cofibrations have genuine pushouts in the section category. -/
theorem actual_pushout_exists (R : CommRingCat.{u}) {A B D : BoundedFlatAffineSections R}
    (i : A ⟶ B) (f : A ⟶ D) (hi : boundedFlatAffineSectionCof R i) :
    ∃ (P : BoundedFlatAffineSections R) (g : B ⟶ P) (j : D ⟶ P), IsPushout i f g j :=
  (boundedFlatAffineSectionWaldhausen R).pushout_exists i f
    ((boundedFlatAffineSectionWaldhausen_cof_iff R i).mpr hi)

/-- Actual coefficient maps preserve actual section pushout squares along pointwise cofibrations. -/
theorem coefficient_preserves_pushout {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {A B D P : BoundedFlatAffineSections R} {i : A ⟶ B} {f : A ⟶ D}
    {g : B ⟶ P} {j : D ⟶ P} (hi : boundedFlatAffineSectionCof R i)
    (h : IsPushout i f g j) :
    IsPushout ((boundedFlatAffineSectionsMap φ).map i) ((boundedFlatAffineSectionsMap φ).map f)
      ((boundedFlatAffineSectionsMap φ).map g) ((boundedFlatAffineSectionsMap φ).map j) :=
  (boundedFlatAffineSectionsMap_exact φ).pushout
    ((boundedFlatAffineSectionWaldhausen_cof_iff R i).mpr hi) h

/-- The Waldhausen choice remains the literal original pointwise zero section. -/
theorem literal_zero_restriction {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffineSectionsMap f).obj (boundedFlatAffineSectionWaldhausen R).zero =
      (boundedFlatAffineSectionWaldhausen S).zero := by
  rw [boundedFlatAffineSectionWaldhausen_zero, boundedFlatAffineSectionsMap_sectionZero,
    boundedFlatAffineSectionWaldhausen_zero]

/-- Both functors of the actual categorical equivalence are exact for the original classes. -/
theorem actual_exact_equivalence (R : CommRingCat.{u}) :
    Waldhausen.IsExact (boundedFlatAffineSectionWaldhausen R).cof
        (boundedFlatAffineSectionWaldhausen R).weq
        (boundedFlatPerfectWaldhausen (Spec R)).cof (boundedFlatPerfectWaldhausen (Spec R)).weq
        (boundedFlatAffineSectionEquivalence R).functor ∧
      Waldhausen.IsExact (boundedFlatPerfectWaldhausen (Spec R)).cof
        (boundedFlatPerfectWaldhausen (Spec R)).weq
        (boundedFlatAffineSectionWaldhausen R).cof (boundedFlatAffineSectionWaldhausen R).weq
        (boundedFlatAffineSectionEquivalence R).inverse :=
  ⟨boundedFlatAffineOriginalEvaluation_exact R,
    boundedFlatAffineSectionEquivalence_inverse_exact R⟩

end QuillenTest.BoundedFlatSectionWaldhausen
