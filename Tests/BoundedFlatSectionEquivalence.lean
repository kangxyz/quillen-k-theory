/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionEquivalence

/-!
# Consumers of the actual bounded-flat section evaluation equivalence

These consumers retain literal original pullback values and recover arbitrary morphisms of the
original bounded-flat category through the proved categorical evaluation equivalence.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
universe u
namespace Quillen.Tests.BoundedFlatSectionEquivalence

/-- Canonical sections use the actual pullback of each original complex at every arrow. -/
theorem actual_pullback_value {R S : CommRingCat.{u}} (h : R ⟶ S)
    (x : BoundedFlatPerfect (Spec R)) :
    ((boundedFlatAffinePullbackSection R x).obj.val.obj (Under.mk h)).fiber =
      (boundedFlatPerfectPullback (Spec.map h)).obj x :=
  boundedFlatAffinePullbackSection_obj h x

/-- Evaluation of a pullback section recovers the original complex by its identity iso. -/
def originalIdentityComparison (R : CommRingCat.{u}) (x : BoundedFlatPerfect (Spec R)) :
    (boundedFlatAffineOriginalEvaluation R).obj (boundedFlatAffinePullbackSection R x) ≅ x :=
  Quillen.CategoryTheory.GrothendieckSections.originalEvaluationSectionIso
    boundedFlatAffinePseudofunctor R x

/-- The declared equivalence retains the actual forward evaluation functor. -/
theorem original_forward_functor (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionEquivalence R).functor = boundedFlatAffineOriginalEvaluation R := rfl

/-- Every original morphism between evaluations has a unique actual vertical section lift. -/
theorem unique_original_morphism (R : CommRingCat.{u}) {s t : BoundedFlatAffineSections R}
    (f : (boundedFlatAffineOriginalEvaluation R).obj s ⟶
      (boundedFlatAffineOriginalEvaluation R).obj t) :
    ∃! a : s ⟶ t, (boundedFlatAffineOriginalEvaluation R).map a = f := by
  refine ⟨(boundedFlatAffineOriginalEvaluation R).preimage f, Functor.map_preimage _ _, ?_⟩
  intro a ha
  apply (boundedFlatAffineOriginalEvaluation R).map_injective
  exact ha.trans (Functor.map_preimage _ _).symm

/-- Every original complex is represented by an actual section under the original evaluation. -/
theorem original_object_representative (R : CommRingCat.{u}) (x : BoundedFlatPerfect (Spec R)) :
    ∃ s : BoundedFlatAffineSections R,
      Nonempty ((boundedFlatAffineOriginalEvaluation R).obj s ≅ x) :=
  ⟨boundedFlatAffinePullbackSection R x, ⟨originalIdentityComparison R x⟩⟩

end Quillen.Tests.BoundedFlatSectionEquivalence
