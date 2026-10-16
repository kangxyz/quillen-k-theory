/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.ExtensionByZero
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedMorphisms
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
/-!
# Genuine derived extension by zero and its adjunction

The actual exact module-sheaf extension by zero induces a triangulated,
shift-compatible functor on the original ambient derived categories.
Localizing the original chain adjunction proves its adjunction to the
existing `derivedRestrict`, retaining both original localization factor
squares and the literal localized unit and counit.

For original complexes the endpoint-normalized Hom equivalence is additive,
preserves the original chain adjunction, and is natural under arbitrary
derived source and target maps. Its inverse is actual derived extension
followed by the original counit. Every integer-shifted source has the same
zero-preserving Hom transport. Full faithfulness of derived extension by
zero follows from its genuine invertible unit. All objects are ambient
module-sheaf derived objects; no perfectness of extended objects is assumed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules (derivedRestrict derivedRestrictFactors)

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes

/-- The standard derived model used to localize the actual sheaf extension by zero. -/
local instance extensionByZeroStandardDerived (X : Scheme.{u}) : HasDerivedCategory.{u + 1}
  X.Modules :=
  HasDerivedCategory.standard _

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The genuine exact sheaf extension by zero on the original ambient derived categories. -/
def derivedExtensionByZero : DerivedCategory U.Modules ⥤ DerivedCategory X.Modules :=
  (AlgebraicGeometry.Scheme.Modules.extensionByZero j).mapDerivedCategory

instance derivedExtensionByZero_additive : (derivedExtensionByZero j).Additive :=
  inferInstanceAs ((AlgebraicGeometry.Scheme.Modules.extensionByZero j).mapDerivedCategory.Additive)

instance derivedExtensionByZeroCommShift : (derivedExtensionByZero j).CommShift ℤ :=
  inferInstanceAs ((AlgebraicGeometry.Scheme.Modules.extensionByZero j).mapDerivedCategory.CommShift
    ℤ)

instance derivedExtensionByZero_isTriangulated : (derivedExtensionByZero j).IsTriangulated :=
  inferInstanceAs ((AlgebraicGeometry.Scheme.Modules.extensionByZero
    j).mapDerivedCategory.IsTriangulated)

/-- Its original localization factorization is the one for the actual exact sheaf functor. -/
def derivedExtensionByZeroFactors :
    DerivedCategory.Q (C := U.Modules) ⋙ derivedExtensionByZero j ≅ extensionByZero j
      ⋙ DerivedCategory.Q (C := X.Modules) :=
  (AlgebraicGeometry.Scheme.Modules.extensionByZero j).mapDerivedCategoryFactors

/-- The localization square comparing actual extension by zero with its derived functor. -/
local instance extensionByZeroLocalizationSquare :
    CatCommSq (extensionByZero j) (DerivedCategory.Q (C := U.Modules))
      (DerivedCategory.Q (C := X.Modules)) (derivedExtensionByZero j) :=
  ⟨(derivedExtensionByZeroFactors j).symm⟩

/-- The localization square comparing actual restriction with its derived functor. -/
local instance restrictLocalizationSquare :
    CatCommSq (restrict j) (DerivedCategory.Q (C := X.Modules)) (DerivedCategory.Q (C := U.Modules))
      (derivedRestrict j) :=
  ⟨(derivedRestrictFactors j).symm⟩

/-- Localizing the genuine chain adjunction gives an adjunction to the original derived restriction.
-/
def derivedExtensionByZeroAdjunction : derivedExtensionByZero j ⊣ derivedRestrict j :=
  (extensionByZeroAdjunction j).localization
    (DerivedCategory.Q (C := U.Modules)) (HomologicalComplex.quasiIso U.Modules (.up ℤ))
    (DerivedCategory.Q (C := X.Modules)) (HomologicalComplex.quasiIso X.Modules (.up ℤ))
    (derivedExtensionByZero j) (derivedRestrict j)

instance derivedRestrict_additive : (derivedRestrict j).Additive :=
  (derivedExtensionByZeroAdjunction j).right_adjoint_additive

/-- The derived unit is exactly the localized original unit with the actual factorization squares.
-/
lemma derivedExtensionByZeroAdjunction_unit_app (K : CochainComplex U.Modules ℤ) :
    (derivedExtensionByZeroAdjunction j).unit.app ((DerivedCategory.Q (C := U.Modules)).obj K) =
      (DerivedCategory.Q (C := U.Modules)).map ((extensionByZeroAdjunction j).unit.app K) ≫
        (derivedRestrictFactors j).inv.app ((extensionByZero j).obj K) ≫
        (derivedRestrict j).map ((derivedExtensionByZeroFactors j).inv.app K) :=
  (extensionByZeroAdjunction j).localization_unit_app
    (DerivedCategory.Q (C := U.Modules)) (HomologicalComplex.quasiIso U.Modules (.up ℤ))
    (DerivedCategory.Q (C := X.Modules)) (HomologicalComplex.quasiIso X.Modules (.up ℤ))
    (derivedExtensionByZero j) (derivedRestrict j) K

/-- The derived counit retains the original chain counit and the same localization squares. -/
lemma derivedExtensionByZeroAdjunction_counit_app (L : CochainComplex X.Modules ℤ) :
    (derivedExtensionByZeroAdjunction j).counit.app ((DerivedCategory.Q (C := X.Modules)).obj L) =
      (derivedExtensionByZero j).map ((derivedRestrictFactors j).hom.app L) ≫
        (derivedExtensionByZeroFactors j).hom.app ((restrict j).obj L) ≫
        (DerivedCategory.Q (C := X.Modules)).map ((extensionByZeroAdjunction j).counit.app L) :=
  (extensionByZeroAdjunction j).localization_counit_app
    (DerivedCategory.Q (C := U.Modules)) (HomologicalComplex.quasiIso U.Modules (.up ℤ))
    (DerivedCategory.Q (C := X.Modules)) (HomologicalComplex.quasiIso X.Modules (.up ℤ))
    (derivedExtensionByZero j) (derivedRestrict j) L

/-- The actual adjunction as an additive Hom equivalence for all derived objects. -/
def derivedExtensionByZeroHomAddEquiv (K : DerivedCategory U.Modules)
    (L : DerivedCategory X.Modules) :
    ((derivedExtensionByZero j).obj K ⟶ L) ≃+ (K ⟶ (derivedRestrict j).obj L) :=
  (derivedExtensionByZeroAdjunction j).homAddEquiv K L

/-- The derived extension unit is invertible on every original derived object. -/
instance derivedExtensionByZero_unit_app_isIso (K : DerivedCategory U.Modules) :
    IsIso ((derivedExtensionByZeroAdjunction j).unit.app K) := by
  let : (DerivedCategory.Q (C := U.Modules)).EssSurj := Localization.essSurj _
    (HomologicalComplex.quasiIso U.Modules (.up ℤ))
  rw [← NatTrans.isIso_app_iff_of_iso (derivedExtensionByZeroAdjunction j).unit
    ((DerivedCategory.Q (C := U.Modules)).objObjPreimageIso K)]
  rw [derivedExtensionByZeroAdjunction_unit_app]
  infer_instance

instance derivedExtensionByZero_unit_isIso : IsIso (derivedExtensionByZeroAdjunction j).unit :=
  NatIso.isIso_of_isIso_app _

/-- Actual derived extension by zero is fully faithful, from its genuine invertible unit. -/
def derivedExtensionByZeroFullyFaithful : (derivedExtensionByZero j).FullyFaithful :=
  (derivedExtensionByZeroAdjunction j).fullyFaithfulLOfIsIsoUnit

/-- Derived extension of a morphism, at the original localized chain-complex endpoints. -/
def extensionByZeroDerivedHom {K K' : CochainComplex U.Modules ℤ}
    (a : (DerivedCategory.Q (C := U.Modules)).obj K ⟶ (DerivedCategory.Q (C := U.Modules)).obj K') :
    (DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K') :=
  (derivedExtensionByZeroFactors j).inv.app K ≫ (derivedExtensionByZero j).map a ≫
    (derivedExtensionByZeroFactors j).hom.app K'

/-- Endpoint-normalized adjunction on the literal original chain-complex localizations. -/
def extensionByZeroDerivedHomEquiv (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ) :
    ((DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L) ≃
      ((DerivedCategory.Q (C := U.Modules)).obj K ⟶ (DerivedCategory.Q (C := U.Modules)).obj
        ((restrict j).obj L)) :=
  { toFun f := (derivedExtensionByZeroAdjunction j).homEquiv _ _
      ((derivedExtensionByZeroFactors j).hom.app K ≫ f) ≫ (derivedRestrictFactors j).hom.app L
    invFun g := (derivedExtensionByZeroFactors j).inv.app K ≫
      ((derivedExtensionByZeroAdjunction j).homEquiv _ _).symm
        (g ≫ (derivedRestrictFactors j).inv.app L)
    left_inv f := by simp [Category.assoc]
    right_inv g := by simp [Category.assoc] }


/-- The normalized Hom equivalence is the original localized unit followed by restriction. -/
lemma extensionByZeroDerivedHomEquiv_eq (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ)
    (f : (DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L) :
    extensionByZeroDerivedHomEquiv j K L f =
      (DerivedCategory.Q (C := U.Modules)).map ((extensionByZeroAdjunction j).unit.app K)
        ≫ restrictDerivedHom j f := by
  change ((derivedExtensionByZeroAdjunction j).unit.app ((DerivedCategory.Q (C := U.Modules)).obj K)
    ≫
    (derivedRestrict j).map ((derivedExtensionByZeroFactors j).hom.app K ≫ f)) ≫
      (derivedRestrictFactors j).hom.app L = _
  rw [derivedExtensionByZeroAdjunction_unit_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (derivedRestrict j).map_comp_assoc, Iso.inv_hom_id_app]
  erw [(derivedRestrict j).map_id]
  rw [Category.id_comp]
  rfl


/-- In particular, the original chain adjunction is preserved exactly by localization. -/
@[simp]
lemma extensionByZeroDerivedHomEquiv_map (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ)
    (f : (extensionByZero j).obj K ⟶ L) :
    extensionByZeroDerivedHomEquiv j K L ((DerivedCategory.Q (C := X.Modules)).map f) =
      (DerivedCategory.Q (C := U.Modules)).map ((extensionByZeroAdjunction j).homEquiv K L f) := by
  rw [extensionByZeroDerivedHomEquiv_eq, restrictDerivedHom_map, ← Functor.map_comp]
  rfl

@[simp]
lemma extensionByZeroDerivedHomEquiv_zero (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ) :
    extensionByZeroDerivedHomEquiv j K L 0 = 0 := by
  simp [extensionByZeroDerivedHomEquiv_eq, restrictDerivedHom]

/-- Extension on original derived arrows recovers the localized original chain map. -/
@[simp]
lemma extensionByZeroDerivedHom_map {K K' : CochainComplex U.Modules ℤ} (a : K ⟶ K') :
    extensionByZeroDerivedHom j ((DerivedCategory.Q (C := U.Modules)).map a) =
      (DerivedCategory.Q (C := X.Modules)).map ((extensionByZero j).map a) := by
  have h := (derivedExtensionByZeroFactors j).hom.naturality a
  change (derivedExtensionByZero j).map ((DerivedCategory.Q (C := U.Modules)).map a) ≫
    (derivedExtensionByZeroFactors j).hom.app K' =
      (derivedExtensionByZeroFactors j).hom.app K ≫
        (DerivedCategory.Q (C := X.Modules)).map ((extensionByZero j).map a) at h
  unfold extensionByZeroDerivedHom
  rw [h]
  simp

/-- Naturality under an arbitrary original derived source arrow. -/
lemma extensionByZeroDerivedHomEquiv_precomp {K K' : CochainComplex U.Modules ℤ}
    (L : CochainComplex X.Modules ℤ)
    (a : (DerivedCategory.Q (C := U.Modules)).obj K' ⟶ (DerivedCategory.Q (C := U.Modules)).obj K)
    (f : (DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L) :
    extensionByZeroDerivedHomEquiv j K' L (extensionByZeroDerivedHom j a ≫ f) =
      a ≫ extensionByZeroDerivedHomEquiv j K L f := by
  change (derivedExtensionByZeroAdjunction j).homEquiv _ _
    ((derivedExtensionByZeroFactors j).hom.app K' ≫
      ((derivedExtensionByZeroFactors j).inv.app K' ≫ (derivedExtensionByZero j).map a ≫
        (derivedExtensionByZeroFactors j).hom.app K) ≫ f) ≫
      (derivedRestrictFactors j).hom.app L = _
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [Adjunction.homEquiv_naturality_left]
  simp only [Category.assoc]
  rfl

/-- Naturality under an arbitrary original derived target arrow. -/
lemma extensionByZeroDerivedHomEquiv_postcomp (K : CochainComplex U.Modules ℤ)
    {L L' : CochainComplex X.Modules ℤ}
    (f : (DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L)
    (b : (DerivedCategory.Q (C := X.Modules)).obj L ⟶ (DerivedCategory.Q (C := X.Modules)).obj L') :
    extensionByZeroDerivedHomEquiv j K L' (f ≫ b) =
      extensionByZeroDerivedHomEquiv j K L f ≫ restrictDerivedHom j b := by
  rw [extensionByZeroDerivedHomEquiv_eq, extensionByZeroDerivedHomEquiv_eq,
    restrictDerivedHom_comp, Category.assoc]

/-- The endpoint-normalized Hom equivalence is additive and in particular reflects zero. -/
def extensionByZeroDerivedHomAddEquiv (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ) :
    ((DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L) ≃+
      ((DerivedCategory.Q (C := U.Modules)).obj K ⟶ (DerivedCategory.Q (C := U.Modules)).obj
        ((restrict j).obj L)) :=
  { extensionByZeroDerivedHomEquiv j K L with
    map_add' f g := by
      simp [extensionByZeroDerivedHomEquiv_eq, restrictDerivedHom, Preadditive.comp_add,
        Preadditive.add_comp] }

@[simp]
lemma extensionByZeroDerivedHomEquiv_eq_zero_iff (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ)
    (f : (DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K) ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L) :
    extensionByZeroDerivedHomEquiv j K L f = 0 ↔ f = 0 :=
  (extensionByZeroDerivedHomAddEquiv j K L).map_eq_zero_iff

/-- Actual shift compatibility identifies the extended shifted source with the shifted original
  source. -/
def extensionByZeroDerivedShiftIso (K : CochainComplex U.Modules ℤ) (n : ℤ) :
    (derivedExtensionByZero j).obj (((DerivedCategory.Q (C := U.Modules)).obj K)⟦n⟧) ≅
      ((DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K))⟦n⟧ :=
  ((derivedExtensionByZero j).commShiftIso n).app ((DerivedCategory.Q (C := U.Modules)).obj K) ≪≫
    (shiftFunctor (DerivedCategory X.Modules) n).mapIso ((derivedExtensionByZeroFactors j).app K)

/-- Shifted-source Hom transport in the original localizations, for every integer shift. -/
def extensionByZeroDerivedShiftHomEquiv (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ) (n : ℤ) :
    (((DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K))⟦n⟧ ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L) ≃
      (((DerivedCategory.Q (C := U.Modules)).obj K)⟦n⟧ ⟶ (DerivedCategory.Q (C := U.Modules)).obj
        ((restrict j).obj L)) where
  toFun f := (derivedExtensionByZeroAdjunction j).homEquiv _ _
    ((extensionByZeroDerivedShiftIso j K n).hom ≫ f) ≫ (derivedRestrictFactors j).hom.app L
  invFun g := (extensionByZeroDerivedShiftIso j K n).inv ≫
    ((derivedExtensionByZeroAdjunction j).homEquiv _ _).symm
      (g ≫ (derivedRestrictFactors j).inv.app L)
  left_inv f := by simp [Category.assoc]
  right_inv g := by simp [Category.assoc]

@[simp]
lemma extensionByZeroDerivedShiftHomEquiv_zero (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ) (n : ℤ) :
    extensionByZeroDerivedShiftHomEquiv j K L n 0 = 0 := by
  change (derivedExtensionByZeroAdjunction j).homEquiv _ _ (_ ≫ 0) ≫ _ = 0
  simp

@[simp]
lemma extensionByZeroDerivedShiftHomEquiv_eq_zero_iff (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ) (n : ℤ)
    (f : ((DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K))⟦n⟧ ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L) :
    extensionByZeroDerivedShiftHomEquiv j K L n f = 0 ↔ f = 0 := by
  rw [← extensionByZeroDerivedShiftHomEquiv_zero j K L n]
  exact (extensionByZeroDerivedShiftHomEquiv j K L n).injective.eq_iff

/-- The inverse normalized adjunction is actual derived extension followed by the original counit.
-/
lemma extensionByZeroDerivedHomEquiv_symm_eq (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ)
    (g : (DerivedCategory.Q (C := U.Modules)).obj K ⟶ (DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj L)) :
    (extensionByZeroDerivedHomEquiv j K L).symm g =
      extensionByZeroDerivedHom j g ≫ (DerivedCategory.Q (C := X.Modules)).map
        ((extensionByZeroAdjunction j).counit.app L)
        := by
  change (derivedExtensionByZeroFactors j).inv.app K ≫
    (derivedExtensionByZero j).map (g ≫ (derivedRestrictFactors j).inv.app L) ≫
      (derivedExtensionByZeroAdjunction j).counit.app ((DerivedCategory.Q (C := X.Modules)).obj L)
        = _
  rw [derivedExtensionByZeroAdjunction_counit_app]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← (derivedExtensionByZero j).map_comp_assoc
    ((derivedRestrictFactors j).inv.app L) ((derivedRestrictFactors j).hom.app L),
    Iso.inv_hom_id_app]
  erw [(derivedExtensionByZero j).map_id]
  simp only [Category.id_comp, extensionByZeroDerivedHom, Category.assoc]

/-- Inverse normalized Hom transport recovers the original localized chain adjoint. -/
@[simp]
lemma extensionByZeroDerivedHomEquiv_symm_map (K : CochainComplex U.Modules ℤ)
    (L : CochainComplex X.Modules ℤ)
    (g : K ⟶ (restrict j).obj L) :
    (extensionByZeroDerivedHomEquiv j K L).symm ((DerivedCategory.Q (C := U.Modules)).map g) =
      (DerivedCategory.Q (C := X.Modules)).map (extensionByZeroMap j g) := by
  rw [extensionByZeroDerivedHomEquiv_symm_eq, extensionByZeroDerivedHom_map,
    ← CategoryTheory.Functor.map_comp, extensionByZeroMap_eq]

/-- Exact target naturality of the shifted Hom equivalence, on arbitrary derived arrows. -/
lemma extensionByZeroDerivedShiftHomEquiv_postcomp (K : CochainComplex U.Modules ℤ)
    {L L' : CochainComplex X.Modules ℤ} (n : ℤ)
    (f : ((DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj K))⟦n⟧ ⟶
      (DerivedCategory.Q (C := X.Modules)).obj L)
    (b : (DerivedCategory.Q (C := X.Modules)).obj L ⟶ (DerivedCategory.Q (C := X.Modules)).obj L') :
    extensionByZeroDerivedShiftHomEquiv j K L' n (f ≫ b) =
      extensionByZeroDerivedShiftHomEquiv j K L n f ≫ restrictDerivedHom j b := by
  change (derivedExtensionByZeroAdjunction j).homEquiv _ _
    ((extensionByZeroDerivedShiftIso j K n).hom ≫ f ≫ b) ≫
      (derivedRestrictFactors j).hom.app L' =
    ((derivedExtensionByZeroAdjunction j).homEquiv _ _
      ((extensionByZeroDerivedShiftIso j K n).hom ≫ f) ≫
        (derivedRestrictFactors j).hom.app L) ≫
      (derivedRestrictFactors j).inv.app L ≫ (derivedRestrict j).map b ≫
        (derivedRestrictFactors j).hom.app L'
  rw [← Category.assoc (extensionByZeroDerivedShiftIso j K n).hom f b,
    Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]


end Quillen.PerfectComplexes
