/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Sections
public import Quillen.CategoryTheory.FiberedCategory.GrothendieckSectionEquivalence

/-!
# Original evaluation of bounded-flat affine sections

Every original bounded-flat complex produces its actual pullback section. Evaluation, with only
the proved base equality transported, is equivalent to the original bounded-flat category.
The section category has larger hom universe, which is retained explicitly by this equivalence.

The pointwise Waldhausen structure, literal chosen-zero preservation, and original spectrum/seed
comparison remain separate. No K-equivalence is inferred from this categorical result alone.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- The section of an original complex consists of its actual coefficient pullbacks. -/
def boundedFlatAffinePullbackSection (R : CommRingCat.{u}) (x : BoundedFlatPerfect (Spec R)) :
    BoundedFlatAffineSections R :=
  Quillen.CategoryTheory.GrothendieckSections.cocartesianSection
    boundedFlatAffinePseudofunctor R x

/-- Concrete evaluation into the original bounded-flat category. -/
def boundedFlatAffineOriginalEvaluation (R : CommRingCat.{u}) :
    BoundedFlatAffineSections R ⥤ BoundedFlatPerfect (Spec R) :=
  Quillen.CategoryTheory.GrothendieckSections.originalEvaluation
    boundedFlatAffinePseudofunctor R

instance instIsEquivalenceBoundedFlatAffineOriginalEvaluation (R : CommRingCat.{u}) :
    (boundedFlatAffineOriginalEvaluation R).IsEquivalence :=
  inferInstanceAs (Quillen.CategoryTheory.GrothendieckSections.originalEvaluation
    boundedFlatAffinePseudofunctor R).IsEquivalence

/-- A proved categorical equivalence retaining the original evaluation functor. -/
def boundedFlatAffineSectionEquivalence (R : CommRingCat.{u}) :
    BoundedFlatAffineSections R ≌ BoundedFlatPerfect (Spec R) :=
  (boundedFlatAffineOriginalEvaluation R).asEquivalence

/-- Every value of the canonical section is the literal original coefficient pullback. -/
theorem boundedFlatAffinePullbackSection_obj {R S : CommRingCat.{u}} (h : R ⟶ S)
    (x : BoundedFlatPerfect (Spec R)) :
    ((boundedFlatAffinePullbackSection R x).obj.val.obj (Under.mk h)).fiber =
      (boundedFlatPerfectPullback (Spec.map h)).obj x := rfl

end Quillen.PerfectComplexes
