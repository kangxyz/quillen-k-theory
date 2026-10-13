/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.InjectiveCounit
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.InjectiveRestriction

/-!
# Original principal sections of affine injective complexes

The actual counit and principal restriction construct the literal comparison
from localized global sections to sections on the principal open. On an actual
lower-bounded injective all-sheaf complex with quasicoherent homology it is a
quasi-isomorphism. Quasicoherent terms and an upper bound are not required.

The scalar-forgotten comparison lands in the original R-module sections.
Its numerator formula is exactly original section restriction. All actual
restriction-section isomorphisms, scalar actions, and counit maps are retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
namespace Quillen.PerfectComplexes.Affine

local instance principalGlobalSections_additive (R : CommRingCat.{u}) (r : R) :
    (moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r))).Additive :=
  Quillen.SchemeSheaf.moduleSpecΓFunctor_additive _


/-- Genuine affine global sections preserve a weak map from a quasicoherent-term complex
to a lower-bounded injective complex with quasicoherent homology. -/
lemma quasiIso_sections_of_quasicoherent_to_injective {R : CommRingCat.{u}}
    {K I : Complex (Spec R)} (a : ℤ)
    (hK : ∀ n, (K.X n).IsQuasicoherent)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) (f : K ⟶ I) [QuasiIso f] :
    QuasiIso ((sectionsComplex R).map f) := by
  have : IsIso (associatedSectionsCounit R K) := by
    rw [associatedSectionsCounit_eq_of_quasicoherent R K hK]
    infer_instance
  let := quasiIso_associatedSectionsCounit I a hbound hinj hqc
  rw [← quasiIso_associated_iff R,
    ← quasiIso_iff_comp_right _ (associatedSectionsCounit R I),
    associatedSectionsCounit_naturality]
  infer_instance

/-- Original homology quasicoherence survives actual open restriction. -/
lemma quasicoherent_homology_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Complex X) (hqc : ∀ n, (K.homology n).IsQuasicoherent) (n : ℤ) :
    (((restrict j).obj K).homology n).IsQuasicoherent := by
  let := hqc n
  exact (SheafOfModules.isQuasicoherent U.ringCatSheaf).prop_of_iso
    (restrictHomologyIso j K n).symm inferInstance

/-- Actual principal localized sections: the canonical localization isomorphism followed
by global sections of the restricted original affine counit. -/
def principalSectionsComparison (R : CommRingCat.{u}) (r : R) :
    moduleSpecΓFunctor (R := R) ⋙ ModuleCat.localizedModuleFunctor (Submonoid.powers r) ⟶
      Scheme.Modules.restrictFunctor (CoherentScheme.principalOpen R r) ⋙
      moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r)) :=
  Functor.whiskerLeft (moduleSpecΓFunctor (R := R)) (CoherentScheme.localizationRestrictionNatIso R
    r).hom ≫
    Functor.whiskerRight
      (Functor.whiskerRight Scheme.Modules.fromTildeΓNatTrans
        (Scheme.Modules.restrictFunctor (CoherentScheme.principalOpen R r)))
        (moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r)))

/-- The literal principal-localized comparison on original complexes. -/
def principalSectionsComplexComparison (R : CommRingCat.{u}) (r : R) (I : Complex (Spec R)) :
    ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).mapHomologicalComplex (.up ℤ)).obj
      ((sectionsComplex R).obj I) ⟶
      (sectionsComplex (CommRingCat.of (Localization.Away r))).obj
        ((restrict (CoherentScheme.principalOpen R r)).obj I) :=
  (NatTrans.mapHomologicalComplex (principalSectionsComparison R r) (.up ℤ)).app I

/-- The comparison is the original localization/restriction isomorphism followed by the
actual restricted counit, as a chain map. -/
lemma principalSectionsComplexComparison_eq (R : CommRingCat.{u}) (r : R) (I : Complex (Spec R)) :
    principalSectionsComplexComparison R r I =
      (NatIso.mapHomologicalComplex (CoherentScheme.localizationRestrictionNatIso R r) (.up
        ℤ)).hom.app
        ((sectionsComplex R).obj I) ≫
      (sectionsComplex (CommRingCat.of (Localization.Away r))).map
        ((restrict (CoherentScheme.principalOpen R r)).map (associatedSectionsCounit R I)) := rfl

/-- Actual scalar-localized global sections compute sections on the principal open for
lower-bounded injective complexes with quasicoherent homology. -/
lemma quasiIso_principalSectionsComplexComparison {R : CommRingCat.{u}} (r : R)
    (I : Complex (Spec R)) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) :
    QuasiIso (principalSectionsComplexComparison R r I) := by
  let j := CoherentScheme.principalOpen R r
  let := quasiIso_associatedSectionsCounit I a hbound hinj hqc
  have hI (n : ℤ) : Injective (((restrict j).obj I).X n) := by
    let := hinj n
    exact SchemeSheaf.injective_restrict j (I.X n)
  have hK (n : ℤ) :
      (((restrict j).obj ((associatedComplex R).obj ((sectionsComplex R).obj I))).X
        n).IsQuasicoherent := by
    change (((tilde.functor R).obj _).restrict j).IsQuasicoherent
    infer_instance
  have hB (n : ℤ) (hn : n < a) : IsZero (((restrict j).obj I).X n) :=
    (Scheme.Modules.restrictFunctor j).map_isZero (hbound n hn)
  have h := quasiIso_sections_of_quasicoherent_to_injective a hK hB hI
    (quasicoherent_homology_restrict j I hqc)
    ((restrict j).map (associatedSectionsCounit R I))
  rw [principalSectionsComplexComparison_eq]
  infer_instance

end Quillen.PerfectComplexes.Affine

open scoped ModuleCat.Algebra
open TopologicalSpace Opposite
namespace Quillen.PerfectComplexes.Affine

local instance principalScalarGlobalSections_additive (R : CommRingCat.{u}) (r : R) :
    (moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r))).Additive :=
  Quillen.SchemeSheaf.moduleSpecΓFunctor_additive _


/-- Actual sections on an open of the affine scheme, with their original R-module structure. -/
abbrev affineSectionsAt (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    (Spec R).Modules ⥤ ModuleCat.{u} R :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op U)

instance affineSectionsAt_additive (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    (affineSectionsAt R U).Additive where
  map_add := by intros; rfl

/-- The original restriction-section identification is R-linear for every module sheaf. -/
def principalRestrictionSectionsEquiv (R : CommRingCat.{u}) (r : R) (M : (Spec R).Modules) :
    moduleSpecΓFunctor.obj (M.restrict (CoherentScheme.principalOpen R r)) ≃ₗ[R]
      (affineSectionsAt R (CoherentScheme.principalOpen R r ''ᵁ ⊤)).obj M where
  __ := AddEquiv.refl _
  map_smul' a m := Scheme.Modules.restrictAppIso_smul_Spec
    (CommRingCat.ofHom (algebraMap R (Localization.Away r))) a m

/-- The original restricted global-section functor, after forgetting localized scalars,
is naturally the original R-module section functor on the open image. -/
def principalRestrictionSectionsImageIso (R : CommRingCat.{u}) (r : R) :
    (Scheme.Modules.restrictFunctor (CoherentScheme.principalOpen R r) ⋙
      moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r))) ⋙
        ModuleCat.restrictScalars (algebraMap R (Localization.Away r)) ≅
    affineSectionsAt R (CoherentScheme.principalOpen R r ''ᵁ ⊤) :=
  NatIso.ofComponents (fun M => (principalRestrictionSectionsEquiv R r M).toModuleIso) (by
    intro M N f
    ext x
    rfl)

lemma principalOpen_imageTop (R : CommRingCat.{u}) (r : R) :
    CoherentScheme.principalOpen R r ''ᵁ ⊤ = PrimeSpectrum.basicOpen r := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact Scheme.Hom.opensRange_localizationAway r

/-- Actual change of open by equality, using the original presheaf maps. -/
def affineSectionsAtCongr (R : CommRingCat.{u}) {U V : (Spec R).Opens} (h : U = V) :
    affineSectionsAt R U ≅ affineSectionsAt R V :=
  NatIso.ofComponents (fun M => (modulesSpecToSheaf.obj M).obj.mapIso (eqToIso h.symm).op) (by
    intro M N f
    exact ((modulesSpecToSheaf.map f).hom.naturality _).symm)

/-- The same genuine scalar comparison with the literal principal basic open as target. -/
def principalRestrictionSectionsIso (R : CommRingCat.{u}) (r : R) :
    (Scheme.Modules.restrictFunctor (CoherentScheme.principalOpen R r) ⋙
      moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r))) ⋙
        ModuleCat.restrictScalars (algebraMap R (Localization.Away r)) ≅
    affineSectionsAt R (PrimeSpectrum.basicOpen r) :=
  principalRestrictionSectionsImageIso R r ≪≫ affineSectionsAtCongr R (principalOpen_imageTop R r)

/-- The original principal-localized section map viewed in the original module category. -/
def principalSectionsScalarComparison (R : CommRingCat.{u}) (r : R) :
    (moduleSpecΓFunctor (R := R) ⋙ ModuleCat.localizedModuleFunctor (Submonoid.powers r)) ⋙
      ModuleCat.restrictScalars (algebraMap R (Localization.Away r)) ⟶
        affineSectionsAt R (PrimeSpectrum.basicOpen r) :=
  Functor.whiskerRight (principalSectionsComparison R r)
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away r))) ≫
      (principalRestrictionSectionsIso R r).hom

/-- Before localization, the actual comparison is exactly the original restriction of sections. -/
lemma principalSectionsComparison_mk (R : CommRingCat.{u}) (r : R)
    (M : (Spec R).Modules) (x : moduleSpecΓFunctor.obj M) :
    (principalRestrictionSectionsEquiv R r M)
      ((principalSectionsComparison R r).app M
        ((moduleSpecΓFunctor.obj M).localizedModuleMkLinearMap (Submonoid.powers r) x)) =
    ((modulesSpecToSheaf.obj M).obj.map
      (homOfLE (show CoherentScheme.principalOpen R r ''ᵁ ⊤ ≤ ⊤ from le_top)).op) x := by
  change (moduleSpecΓFunctor.map
    ((Scheme.Modules.restrictFunctor (CoherentScheme.principalOpen R r)).map M.fromTildeΓ))
      ((CoherentScheme.localizationRestrictionIso R r (moduleSpecΓFunctor.obj M)).hom
        ((moduleSpecΓFunctor.obj M).localizedModuleMkLinearMap (Submonoid.powers r) x)) = _
  rw [CoherentScheme.localizationRestrictionIso_hom_apply]
  exact ConcreteCategory.congr_hom
    (Scheme.Modules.toOpen_fromTildeΓ_app M (CoherentScheme.principalOpen R r ''ᵁ ⊤)) x

/-- The scalar-forgotten comparison retains the actual section restriction on every numerator. -/
lemma principalSectionsScalarComparison_mk (R : CommRingCat.{u}) (r : R)
    (M : (Spec R).Modules) (x : moduleSpecΓFunctor.obj M) :
    (principalSectionsScalarComparison R r).app M
      ((moduleSpecΓFunctor.obj M).localizedModuleMkLinearMap (Submonoid.powers r) x) =
    ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op) x := by
  change ((modulesSpecToSheaf.obj M).obj.map (eqToHom (principalOpen_imageTop R r).symm).op)
    ((principalRestrictionSectionsEquiv R r M)
      ((principalSectionsComparison R r).app M
        ((moduleSpecΓFunctor.obj M).localizedModuleMkLinearMap (Submonoid.powers r) x))) = _
  rw [principalSectionsComparison_mk, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The actual principal comparison with both source and target in the original R-module category.
-/
def principalSectionsScalarComplexComparison (R : CommRingCat.{u}) (r : R)
    (I : Complex (Spec R)) :=
  (NatTrans.mapHomologicalComplex (principalSectionsScalarComparison R r) (.up ℤ)).app I

/-- The original R-module map is the scalar-forgotten geometric comparison followed by
its genuine section identification. -/
lemma principalSectionsScalarComplexComparison_eq (R : CommRingCat.{u}) (r : R)
    (I : Complex (Spec R)) :
    principalSectionsScalarComplexComparison R r I =
      ((ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).mapHomologicalComplex (.up
        ℤ)).map
        (principalSectionsComplexComparison R r I) ≫
      (NatIso.mapHomologicalComplex (principalRestrictionSectionsIso R r) (.up ℤ)).hom.app I := rfl

/-- Actual principal localization is a weak equivalence in the original R-module category. -/
lemma quasiIso_principalSectionsScalarComplexComparison {R : CommRingCat.{u}} (r : R)
    (I : Complex (Spec R)) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) :
    QuasiIso (principalSectionsScalarComplexComparison R r I) := by
  let := quasiIso_principalSectionsComplexComparison r I a hbound hinj hqc
  rw [principalSectionsScalarComplexComparison_eq]
  infer_instance

end Quillen.PerfectComplexes.Affine
