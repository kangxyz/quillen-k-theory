/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.FullOpenPseudofunctor
public import Quillen.Aglib.CategoryTheory.FiberedCategory.GrothendieckSectionEquivalence

/-!
# Actual full-open section evaluation

Identity evaluation is the original Grothendieck-section equivalence, with its full original object and hom universes.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Original identity evaluation into the specified full-open fiber category. -/
def boundedFlatAffineFullOpenOriginalEvaluation (a : Under R) :
    BoundedFlatAffineFullOpenSections j a ⥤ BoundedFlatPerfect (openSpace j a) :=
  Quillen.CategoryTheory.GrothendieckSections.originalEvaluation
    (boundedFlatAffineFullOpenPseudofunctor j) a

instance instIsEquivalenceBoundedFlatAffineFullOpenOriginalEvaluation (a : Under R) :
    (boundedFlatAffineFullOpenOriginalEvaluation j a).IsEquivalence :=
  inferInstanceAs (Quillen.CategoryTheory.GrothendieckSections.originalEvaluation
    (boundedFlatAffineFullOpenPseudofunctor j) a).IsEquivalence

/-- The original evaluation functor is the actual forward equivalence. -/
def boundedFlatAffineFullOpenSectionEquivalence (a : Under R) :
    BoundedFlatAffineFullOpenSections j a ≌ BoundedFlatPerfect (openSpace j a) :=
  (boundedFlatAffineFullOpenOriginalEvaluation j a).asEquivalence

end Quillen.PerfectComplexes

end

end
