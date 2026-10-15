/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionFullOpenRestriction

/-!
# The actual image zero of full-open restriction

The original section zero is sent to its specified image zero, with its actual zero
universal property inherited from exactness of the unchanged restriction functor.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation

/-- The image of the unchanged original section zero is the specified target image zero. -/
def boundedFlatAffineSectionFullOpenImageZero (a : Under R) :
    BoundedFlatPerfect (openSpace j a) :=
  (boundedFlatAffineSectionFullOpenRestriction j a).obj
    (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).zero

/-- The specified image zero retains its genuine universal property. -/
theorem isZero_boundedFlatAffineSectionFullOpenImageZero (a : Under R) :
    IsZero (boundedFlatAffineSectionFullOpenImageZero j a) :=
  (boundedFlatAffineSectionFullOpenRestriction_exact j a).zero
    (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).isZero

end Quillen.PerfectComplexes
