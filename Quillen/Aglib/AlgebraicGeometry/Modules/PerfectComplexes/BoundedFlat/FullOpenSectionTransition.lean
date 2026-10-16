/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.FullOpenSectionEvaluation
public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianSectionTransition

/-!
# Original full-open evaluation transition

Coefficient reindexing compares identity evaluation with the original actual geometric pullback by the same section transition.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineFullOpenOriginalEvaluation

/-- The original transition, with its actual coefficient-evaluation comparison. -/
def boundedFlatAffineFullOpenSectionCoefficientIso {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenSectionsMap j f ⋙
        boundedFlatAffineFullOpenOriginalEvaluation j b ≅
      boundedFlatAffineFullOpenOriginalEvaluation j a ⋙
        boundedFlatPerfectPullback (openMap j f) := by
  unfold boundedFlatAffineFullOpenOriginalEvaluation
  exact eqToIso (Quillen.CategoryTheory.GrothendieckSections.originalEvaluation_reindex
    (boundedFlatAffineFullOpenPseudofunctor j) a f) ≪≫
  (Quillen.CategoryTheory.GrothendieckSections.originalEvaluationTransitionIso
    (boundedFlatAffineFullOpenPseudofunctor j) a (Under.mk f)).symm

end Quillen.PerfectComplexes

end

end
