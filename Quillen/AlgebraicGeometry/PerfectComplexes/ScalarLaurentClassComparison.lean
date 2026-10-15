/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.AutomorphismKOne
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberKOneNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.Single

/-! Restriction of the original forward scalar square to an independent fine unit K-one class.
The fine class is built from the actual global-unit automorphism. The old source component,
canonical K-map rebasing and inverse orientation of the cofiber class are retained. -/

@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace Quillen.PerfectComplexes

/-- The independent fine K-one class of the original global-unit automorphism. -/
def perfectGlobalUnitKOneClass (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ) (K : Perfect X) :
    PerfectK X 1 :=
  (perfectWaldhausen X).automorphismKOneClass ((perfectGlobalUnitIso X q).app K)

/-- The fine unit class is independent of a displayed isomorphic presentation of its object. -/
theorem perfectGlobalUnitKOneClass_iso (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ)
    {K L : Perfect X} (e : K ≅ L) :
    perfectGlobalUnitKOneClass X q K = perfectGlobalUnitKOneClass X q L := by
  apply (perfectWaldhausen X).weakEndomorphismKOneClass_iso e
    ((perfectGlobalUnitIso X q).hom.app K) ((perfectGlobalUnitIso X q).hom.app L)
  simpa only [Functor.id_map] using ((perfectGlobalUnitIso X q).hom.naturality e.hom).symm

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (K : Perfect X) (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

include hq in
/-- The original relative scalar arrow restricts to the actual independent fine unit arrow. -/
theorem perfectRestrict_scalar_eq_globalUnit :
    (perfectRestrict j).map ((perfectGlobalScalar X r).app K) =
      (perfectGlobalUnitIso U q).hom.app ((perfectRestrict j).obj K) := by
  apply (locallyPerfect U).ι.map_injective
  rw [perfectGlobalUnitIso, Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  exact restrict_map_complexGlobalScalar_unit j r q hq K.obj

/-- The normalized forward scalar square maps to the independent unit class through the original
public restriction K-map, retaining its canonical zero rebase and object-component transport. -/
theorem perfectScalarForwardKOneClass_restrict :
    perfectOpenKRestrict j 1 (perfectScalarForwardKOneClass j K r q hq) =
      perfectGlobalUnitKOneClass U q ((perfectRestrict j).obj K) := by
  exact (KMap_weakEndomorphismKOneClass (V := perfectOpenWeakWaldhausen j)
    (W := perfectWaldhausen U) (perfectOpenRestrict_waldhausenExact j)
    ((perfectGlobalScalar X r).app K) (perfectGlobalScalar_openWeak j r q hq K)).trans
      ((perfectWaldhausen U).weakEndomorphismKOneClass_congr
        (perfectRestrict_scalar_eq_globalUnit j K r q hq) _ _)

/-- The accepted inverse cofiber orientation remains inverse after the original restriction. -/
theorem perfectScalarCofiberBoundaryKOneClass_restrict :
    perfectOpenKRestrict j 1 (perfectScalarCofiberBoundaryKOneClass j K r q hq) =
      (perfectGlobalUnitKOneClass U q ((perfectRestrict j).obj K))⁻¹ := by
  rw [perfectScalarCofiberBoundaryKOneClass_eq_inv, map_inv,
    perfectScalarForwardKOneClass_restrict]

/-- The genuine rank-one structure sheaf, as its original degree-zero perfect complex. -/
def rankOnePerfect (X : Scheme.{u}) : Perfect X := by
  let M := SheafOfModules.unit X.ringCatSheaf
  letI : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X M := by
    let e : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Unit) ≅ M :=
      coproductUniqueIso _
    exact AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_of_iso e
  exact ⟨(CochainComplex.singleFunctor X.Modules 0).obj M,
    locallyPerfect_of_strictPerfect (single_strictPerfect_int M 0)⟩

/-- The original open restriction of the structure single is canonically the structure single. -/
def rankOnePerfectRestrictIso : (perfectRestrict j).obj (rankOnePerfect X) ≅ rankOnePerfect U :=
  (locallyPerfect U).isoMk
    (((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.restrictFunctor j) (.up ℤ) 0).app
        (SheafOfModules.unit X.ringCatSheaf)) ≪≫
      (CochainComplex.singleFunctor U.Modules 0).mapIso (Scheme.Modules.restrictUnitIso j))

/-- Rank one uses the actual structure sheaf on the open, not a chosen matrix presentation. -/
theorem perfectScalarForwardKOneClass_restrict_rankOne :
    perfectOpenKRestrict j 1 (perfectScalarForwardKOneClass j (rankOnePerfect X) r q hq) =
      perfectGlobalUnitKOneClass U q (rankOnePerfect U) := by
  rw [perfectScalarForwardKOneClass_restrict]
  exact perfectGlobalUnitKOneClass_iso U q (rankOnePerfectRestrictIso j)

/-- The structure-sheaf cofiber boundary has the inverse of the actual forward unit class. -/
theorem perfectScalarCofiberBoundaryKOneClass_restrict_rankOne :
    perfectOpenKRestrict j 1
        (perfectScalarCofiberBoundaryKOneClass j (rankOnePerfect X) r q hq) =
      (perfectGlobalUnitKOneClass U q (rankOnePerfect U))⁻¹ := by
  rw [perfectScalarCofiberBoundaryKOneClass_eq_inv, map_inv,
    perfectScalarForwardKOneClass_restrict_rankOne]

open AlgebraicGeometry.Scheme.PolynomialLaurent in
/-- The original forward polynomial coordinate gives the actual forward Laurent unit class. -/
theorem polynomialScalarForwardKOneClass_restrict (R : CommRingCat.{u})
    (K : Perfect (Spec (.of (Polynomial R)))) :
    perfectOpenKRestrict (laurentPlus R) 1
        (perfectScalarForwardKOneClass (laurentPlus R) K
          (polynomialGlobalCoordinate R) (laurentGlobalUnit R)
          (polynomialGlobalCoordinate_laurentPlus R)) =
      perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
        ((perfectRestrict (laurentPlus R)).obj K) :=
  perfectScalarForwardKOneClass_restrict _ _ _ _ _

open AlgebraicGeometry.Scheme.PolynomialLaurent in
/-- The affine client keeps the rank-one structure object and the original T unit. -/
theorem polynomialScalarForwardKOneClass_restrict_rankOne (R : CommRingCat.{u}) :
    perfectOpenKRestrict (laurentPlus R) 1
        (perfectScalarForwardKOneClass (laurentPlus R)
          (rankOnePerfect (Spec (.of (Polynomial R))))
          (polynomialGlobalCoordinate R) (laurentGlobalUnit R)
          (polynomialGlobalCoordinate_laurentPlus R)) =
      perfectGlobalUnitKOneClass _ (laurentGlobalUnit R)
        (rankOnePerfect (Spec (.of (LaurentPolynomial R)))) :=
  perfectScalarForwardKOneClass_restrict_rankOne _ _ _ _

end Quillen.PerfectComplexes
