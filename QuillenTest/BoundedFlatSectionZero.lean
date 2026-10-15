/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionZero

/-!
# Consumers of the original pointwise chosen-zero section

The existing Waldhausen zero is retained under actual evaluation and strict coefficient maps.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.BoundedFlatSectionZero

open Quillen

/-- The entire pointwise section uses the already chosen original zero at its target. -/
theorem original_zero_at_every_arrow {R S : CommRingCat.{u}} (f : R ⟶ S) :
    ((boundedFlatAffineSectionZero R).obj.val.obj (Under.mk f)).fiber =
      (boundedFlatPerfectWaldhausen (Spec S)).zero := rfl

/-- Original evaluation has literal, rather than merely isomorphic, zero preservation. -/
theorem original_zero_evaluation (R : CommRingCat.{u}) :
    (boundedFlatAffineOriginalEvaluation R).obj (boundedFlatAffineSectionZero R) =
      (boundedFlatPerfectWaldhausen (Spec R)).zero :=
  boundedFlatAffineOriginalEvaluation_sectionZero R

/-- Two actual coefficient restrictions preserve the same specified zero section. -/
theorem two_coefficient_zero_restrictions {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionsMap g).obj
      ((boundedFlatAffineSectionsMap f).obj (boundedFlatAffineSectionZero R)) =
      boundedFlatAffineSectionZero T := by
  rw [boundedFlatAffineSectionsMap_sectionZero, boundedFlatAffineSectionsMap_sectionZero]

/-- The section has the actual zero universal property in the strict section category. -/
theorem original_section_isZero (R : CommRingCat.{u}) :
    IsZero (boundedFlatAffineSectionZero R) := isZero_boundedFlatAffineSectionZero R

end QuillenTest.BoundedFlatSectionZero
