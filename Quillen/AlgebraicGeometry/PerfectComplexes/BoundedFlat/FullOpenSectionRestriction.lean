/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.FiberedCategory.GrothendieckUnderRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenRestrictionNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Sections

/-!
# Original full-open restriction of actual affine sections

The actual section is restricted on its original coefficient fibers and arrows. The canonical
identity-on-fibers rebracketing and the original open-pair strong transformation then give
its full-open section. The generic construction proves cocartesianness using those actual
maps, without choosing an inverse evaluation functor.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
attribute [local irreducible] boundedFlatPerfectPseudofunctor
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Restrict the actual source section on its original fibers and original arrows. -/
def boundedFlatAffineFullOpenSectionRestriction (a : Under R) :
    BoundedFlatAffineSections a.right ⥤ BoundedFlatAffineFullOpenSections j a :=
  Quillen.CategoryTheory.GrothendieckUnderRestriction.sectionFunctor
    Scheme.Spec.rightOp boundedFlatPerfectPseudofunctor R
    (boundedFlatAffineFullOpenPseudofunctor j)
    (boundedFlatAffineFullOpenRestrictionStrongTrans j) a

end Quillen.PerfectComplexes
