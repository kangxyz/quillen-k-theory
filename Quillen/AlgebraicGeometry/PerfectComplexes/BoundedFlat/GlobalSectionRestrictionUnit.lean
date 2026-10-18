/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionUnit
public import Quillen.Aglib.CategoryTheory.FiberedCategory.SectionChangeIndexUnit

/-! # Actual scalar preservation for coefficient restriction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.FunctorIdentityAutomorphism
open CategoryTheory.SectionChangeIndex
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- Actual coefficient restriction preserves the original geometric scalar on every section. -/
theorem coefficientRestriction_unit_preserves (R : CommRingCat.{u}) (i : Index R)
    (r : (Γ(space i, ⊤))ˣ) :
    Preserves ((coefficientRestriction R).app i).functor
      (globalUnit ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj i) r)
      (boundedFlatCoefficientSectionUnitIso i r) := by
  exact restriction_lift_preserves boundedFlatPerfectPseudofunctor
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R) i
    (boundedFlatPerfectGlobalUnitIso (space i) r)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
