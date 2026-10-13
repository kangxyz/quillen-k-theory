/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionEvaluation

/-!
# Consumers of original section-transition evaluation

The original geometric pullback and the actual vertical section morphisms appear in the
naturality square. Coefficient reindexing retains both identity and arbitrary-arrow evaluations.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
universe u
namespace QuillenTest.BoundedFlatSectionEvaluation

open Quillen

/-- Every actual section transition compares original pullback with the original fiber. -/
def originalPullbackComparison {R S : CommRingCat.{u}} (f : R ⟶ S)
    (s : BoundedFlatAffineSections R) :
    (boundedFlatPerfectPullback (Spec.map f)).obj
        ((boundedFlatAffineOriginalEvaluation R).obj s) ≅
      (boundedFlatAffineEvaluationAt R (Under.mk f)).obj s :=
  (boundedFlatAffineEvaluationPullbackIso R (Under.mk f)).app s

/-- Naturality retains an arbitrary actual vertical section morphism. -/
theorem original_pullback_square {R S : CommRingCat.{u}} (f : R ⟶ S)
    {s t : BoundedFlatAffineSections R} (a : s ⟶ t) :
    (boundedFlatPerfectPullback (Spec.map f)).map
        ((boundedFlatAffineOriginalEvaluation R).map a) ≫
        (originalPullbackComparison f t).hom =
      (originalPullbackComparison f s).hom ≫
        (boundedFlatAffineEvaluationAt R (Under.mk f)).map a :=
  boundedFlatAffineEvaluationPullbackIso_naturality R a (Under.mk f)

/-- Restriction and identity evaluation give the literal original coefficient evaluation. -/
theorem coefficient_evaluation {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionsMap f ⋙ boundedFlatAffineOriginalEvaluation S =
      boundedFlatAffineEvaluationAt R (Under.mk f) :=
  boundedFlatAffineSectionsMap_comp_evaluation f

/-- An independent second coefficient arrow is retained under reindexing. -/
theorem arbitrary_arrow_evaluation {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedFlatAffineSectionsMap f ⋙ boundedFlatAffineEvaluationAt S (Under.mk g) =
      boundedFlatAffineEvaluationAt R (Under.mk (f ≫ g)) :=
  boundedFlatAffineSectionsMap_comp_evaluationAt f (Under.mk g)

end QuillenTest.BoundedFlatSectionEvaluation
