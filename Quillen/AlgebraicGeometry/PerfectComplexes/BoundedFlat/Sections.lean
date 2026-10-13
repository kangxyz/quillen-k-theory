/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Pseudofunctor
public import Quillen.CategoryTheory.FiberedCategory.CocartesianSections
public import Mathlib.CategoryTheory.Bicategory.Grothendieck

/-!
# Actual bounded-flat affine cocartesian sections

The Grothendieck construction uses the original bounded-flat categories and the proved geometric
pseudofunctor. Sections over the coslice reindex literally, yielding a strict category-valued ring
diagram. Evaluation lands in the actual fiber of the original Grothendieck projection.

An evaluation equivalence, the Waldhausen structure and zero preservation, and the comparison of
the original geometric seed transition remain separate obligations. In particular this owner does
not yet instantiate the strict spectrum-valued Bass endofunctor.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.CategoryTheory.StrictSections
universe u
namespace Quillen.PerfectComplexes

/-- The actual Grothendieck total category of bounded-flat affine pullback. -/
abbrev BoundedFlatAffineTotal := Pseudofunctor.Grothendieck boundedFlatAffinePseudofunctor.{u}

/-- The original projection to the coefficient ring. -/
def boundedFlatAffineProjection : BoundedFlatAffineTotal.{u} ⥤ CommRingCat.{u} :=
  Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor

/-- Actual cocartesian sections, with vertical natural transformations as morphisms. -/
abbrev BoundedFlatAffineSections (R : CommRingCat.{u}) :=
  underCocartesian boundedFlatAffineProjection R

/-- Coefficient change is literal restriction of coslice indices. -/
def boundedFlatAffineSectionsMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    BoundedFlatAffineSections R ⥤ BoundedFlatAffineSections S :=
  underCocartesianReindex boundedFlatAffineProjection f

/-- A strict category-valued diagram built from the actual geometric pseudofunctor. -/
def boundedFlatAffineSectionsFunctor : CommRingCat.{u} ⥤ Cat where
  obj R := ↧(BoundedFlatAffineSections R)
  map f := (boundedFlatAffineSectionsMap f).toCatHom
  map_id R := by
    apply Cat.Hom.ext
    exact underCocartesianReindex_id boundedFlatAffineProjection R
  map_comp f g := by
    apply Cat.Hom.ext
    exact underCocartesianReindex_comp boundedFlatAffineProjection f g

/-- Evaluation at the original identity arrow, into the actual original Grothendieck fiber. -/
def boundedFlatAffineSectionsEvaluation (R : CommRingCat.{u}) :
    BoundedFlatAffineSections R ⥤ Functor.Fiber boundedFlatAffineProjection R :=
  underCocartesianEvaluation boundedFlatAffineProjection R

end Quillen.PerfectComplexes
