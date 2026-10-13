/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionEquivalence
public import Quillen.CategoryTheory.FiberedCategory.CocartesianSectionTransition

/-!
# Original pullback comparison for bounded-flat section evaluation

The comparison uses the actual section transition from the identity to the coefficient arrow.
Its invertibility and naturality follow from strong cocartesianness and original section laws.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.CategoryTheory.GrothendieckSections
universe u
namespace Quillen.PerfectComplexes

/-- Evaluation at an actual coefficient arrow retains the original target fiber. -/
def boundedFlatAffineEvaluationAt (R : CommRingCat.{u}) (j : Under R) :
    BoundedFlatAffineSections R ⥤ BoundedFlatPerfect (Spec j.right) :=
  originalEvaluationAt boundedFlatAffinePseudofunctor R j

/-- The actual original transition compares geometric pullback with evaluation at the arrow. -/
def boundedFlatAffineEvaluationPullbackIso (R : CommRingCat.{u}) (j : Under R) :
    boundedFlatAffineOriginalEvaluation R ⋙ boundedFlatPerfectPullback (Spec.map j.hom) ≅
      boundedFlatAffineEvaluationAt R j :=
  originalEvaluationTransitionIso boundedFlatAffinePseudofunctor R j

/-- At the identity arrow the evaluation functor is the original identity evaluation. -/
theorem boundedFlatAffineEvaluationAt_id (R : CommRingCat.{u}) :
    boundedFlatAffineEvaluationAt R (Under.mk (𝟙 R)) =
      boundedFlatAffineOriginalEvaluation R := rfl

/-- Naturality retains the actual original geometric pullback on morphisms. -/
theorem boundedFlatAffineEvaluationPullbackIso_naturality (R : CommRingCat.{u})
    {s t : BoundedFlatAffineSections R} (a : s ⟶ t) (j : Under R) :
    (boundedFlatPerfectPullback (Spec.map j.hom)).map
        ((boundedFlatAffineOriginalEvaluation R).map a) ≫
        (boundedFlatAffineEvaluationPullbackIso R j).hom.app t =
      (boundedFlatAffineEvaluationPullbackIso R j).hom.app s ≫
        (boundedFlatAffineEvaluationAt R j).map a :=
  (boundedFlatAffineEvaluationPullbackIso R j).hom.naturality a

/-- Coefficient restriction followed by evaluation is the actual arrow evaluation. -/
theorem boundedFlatAffineSectionsMap_comp_evaluation {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionsMap f ⋙ boundedFlatAffineOriginalEvaluation S =
      boundedFlatAffineEvaluationAt R (Under.mk f) :=
  originalEvaluation_reindex boundedFlatAffinePseudofunctor R f

/-- Evaluation after coefficient restriction retains the full reindexed coefficient arrow. -/
theorem boundedFlatAffineSectionsMap_comp_evaluationAt {R S : CommRingCat.{u}}
    (f : R ⟶ S) (j : Under S) :
    boundedFlatAffineSectionsMap f ⋙ boundedFlatAffineEvaluationAt S j =
      boundedFlatAffineEvaluationAt R ((Under.map f).obj j) :=
  originalEvaluationAt_reindex boundedFlatAffinePseudofunctor R f j

end Quillen.PerfectComplexes
