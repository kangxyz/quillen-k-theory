/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedHom.OpenUnion
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
/-! # Original derived zero objects under restriction and stabilization

The literal derived restriction comparisons transport vanishing across open
inclusions. The actual biproduct and shift comparisons preserve vanishing
under stabilization, with no boundedness, perfection, or quasicoherence input.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules (derivedRestrict derivedRestrictFactors)

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The actual complex stabilization remains zero in the original derived category. -/
lemma isZero_toDerived_stabilization_of_isZero {X : Scheme.{u}} {E : CochainComplex X.Modules ℤ}
    (hE : IsZero ((DerivedCategory.Q (C := X.Modules)).obj E)) :
    IsZero ((DerivedCategory.Q (C := X.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧)) := by
  let Q := DerivedCategory.Q (C := X.Modules)
  let : PreservesBinaryBiproducts Q := preservesBinaryBiproducts_of_preservesBiproducts _
  have hs : IsZero (Q.obj (E⟦(1 : ℤ)⟧)) :=
    ((shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map_isZero hE).of_iso
      ((Q.commShiftIso (1 : ℤ)).app E)
  exact ((biprod_isZero_iff _ _).mpr ⟨hE, hs⟩).of_iso (Q.mapBiprod E (E⟦(1 : ℤ)⟧))

/-- Original derived zero objects remain zero under actual open restriction. -/
lemma isZero_toDerived_restrict_of_isZero {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {E : CochainComplex X.Modules ℤ}
    (hE : IsZero ((DerivedCategory.Q (C := X.Modules)).obj E)) :
    IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj E)) :=
  ((derivedRestrict j).map_isZero hE).of_iso ((derivedRestrictFactors j).app E).symm

/-- Acyclicity on an actual open is inherited by every smaller actual open,
with the original nested restriction comparisons. -/
lemma isZero_restrict_homOfLE_of_le {X : Scheme.{u}} {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W) (E : CochainComplex W.toScheme.Modules ℤ)
    (hE : IsZero ((DerivedCategory.Q (C := V.toScheme.Modules)).obj
      ((restrict (X.homOfLE hVW)).obj E))) :
    IsZero ((DerivedCategory.Q (C := U.toScheme.Modules)).obj
      ((restrict (X.homOfLE (hUV.trans hVW))).obj E)) := by
  let e := (restrictCompIso (X.homOfLE hUV) (X.homOfLE hVW) ≪≫
    eqToIso (restrict_congr (X.homOfLE_homOfLE hUV hVW))).app E
  exact (isZero_toDerived_restrict_of_isZero (X.homOfLE hUV) hE).of_iso
    ((DerivedCategory.Q (C := U.toScheme.Modules)).mapIso e).symm

end Quillen.PerfectComplexes
