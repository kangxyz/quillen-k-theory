/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.Basic


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenWeakImage
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # The original derived-saturated restriction image

This is an actual full subcategory of the original perfect chain category.
Its objects retain an isomorphism in the ORIGINAL ambient derived category.
No quasi-isomorphism from a restriction to the unchanged target is inferred.
The explicit geometric complement belongs to this derived-saturated image;
closure and approximation are established separately from actual roofs.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- A one-arrow witnessed object belongs to the saturated target. -/
theorem of_weakImage {E : Perfect U}
    (hE : Waldhausen.ApproximationImage.objects (perfectWaldhausen U) (perfectRestrict j) E) :
    objects j E := by
  obtain ⟨P, q, hq⟩ := hE
  have : QuasiIso q.hom := hq
  exact ⟨P.obj, P.property, ⟨asIso ((DerivedCategory.Q (C := U.Modules)).map q.hom)⟩⟩

end Quillen.PerfectComplexes.OpenDerivedImage
