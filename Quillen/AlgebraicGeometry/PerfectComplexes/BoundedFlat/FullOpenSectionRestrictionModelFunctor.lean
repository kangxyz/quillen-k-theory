/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenDiagram

/-!
# The full-open restriction in its actual Model categories

This typed functor interface uses the existing original source Model diagram object and shares
the source and target Model category expressions used by
exactness and chosen-zero preservation. Its object and arrow maps are exactly the original
full-open section restriction.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original restriction, typed in precisely the two actual Model categories. -/
def boundedFlatAffineFullOpenSectionRestrictionModelFunctor (a : Under R) :
    (boundedFlatAffineSectionOpenModelFunctor j).obj a ⥤
      boundedFlatAffineFullOpenSectionModel j a :=
  boundedFlatAffineFullOpenSectionRestriction j a

/-- The Model-typed interface retains the original restriction functor literally. -/
theorem boundedFlatAffineFullOpenSectionRestrictionModelFunctor_eq (a : Under R) :
    boundedFlatAffineFullOpenSectionRestrictionModelFunctor j a =
      boundedFlatAffineFullOpenSectionRestriction j a := rfl

end Quillen.PerfectComplexes
