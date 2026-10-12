/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionZero

/-! Original-map consumers of literal full-open section-zero preservation. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.Tests.FullOpenSectionRestrictionZero
open Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The unchanged original restriction sends the entire actual zero section to its target. -/
theorem wholeSection (a : Under R) :
    (boundedFlatAffineFullOpenSectionRestriction j a).obj
        (boundedFlatAffineSectionZero a.right) =
      boundedFlatAffineFullOpenSectionZero j a :=
  boundedFlatAffineFullOpenSectionRestriction_sectionZero j a

/-- Every original total object, not just its identity evaluation, is retained literally. -/
theorem indexedObject (a : Under R) (i : Under a) :
    (((boundedFlatAffineFullOpenSectionRestriction j a).obj
        (boundedFlatAffineSectionZero a.right)).obj.val).obj i =
      (boundedFlatAffineFullOpenSectionZero j a).obj.val.obj i :=
  boundedFlatAffineFullOpenSectionRestriction_zero_obj j a i

/-- Actual coefficient reindexing preserves the same restricted zero section. -/
theorem coefficientZero {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineFullOpenSectionsMap j f).obj
        ((boundedFlatAffineFullOpenSectionRestriction j a).obj
          (boundedFlatAffineSectionZero a.right)) =
      boundedFlatAffineFullOpenSectionZero j b := by
  rw [boundedFlatAffineFullOpenSectionRestriction_sectionZero,
    boundedFlatAffineFullOpenSectionsMap_sectionZero]

end Quillen.Tests.FullOpenSectionRestrictionZero
