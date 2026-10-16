/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalSections

/-!
# Actual localized section maps and shrinking-open naturality

For every original open V, the actual localization universal property gives
Gamma(V)[1/r] to Gamma(V intersect D(r)). The correct restricted scalar action
is identified explicitly. The maps are natural in the sheaf and in shrinking
V, and the resulting chain maps factor the literal section restrictions
through their original numerator maps. No acyclicity, quasicoherence or
compactness is used to construct them.

On the ambient affine open the map agrees with the genuine principal
comparison, hence is weak for lower-bounded injective complexes with
quasicoherent homology. Finite-union extension is a separate gluing argument.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped ModuleCat.Algebra
namespace Quillen.PerfectComplexes.Affine

/-- Scalar localization followed by restriction to the original coefficient ring. -/
abbrev scalarLocalize (R : CommRingCat.{u}) (r : R) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ModuleCat.localizedModuleFunctor (Submonoid.powers r) ⋙
    ModuleCat.restrictScalars (algebraMap R (Localization.Away r))

/-- The canonical scalar action identifies the direct localized module with restricted scalars. -/
def scalarLocalizeEquiv (R : CommRingCat.{u}) (r : R) (M : ModuleCat.{u} R) :
    M.localizedModule (Submonoid.powers r) ≃ₗ[R] (scalarLocalize R r).obj M where
  __ := AddEquiv.refl _
  map_smul' a x := by
    change a • x = algebraMap R (Localization.Away r) a • x
    exact (IsScalarTower.algebraMap_smul (Localization.Away r) a x).symm

/-- The original localization numerator, with the actual restricted scalar module structure. -/
def scalarLocalizeMk (R : CommRingCat.{u}) (r : R) (M : ModuleCat.{u} R) :
    M →ₗ[R] (scalarLocalize R r).obj M :=
  (scalarLocalizeEquiv R r M).toLinearMap.comp (M.localizedModuleMkLinearMap (Submonoid.powers r))

instance scalarLocalizeMk_isLocalized (R : CommRingCat.{u}) (r : R) (M : ModuleCat.{u} R) :
    IsLocalizedModule (Submonoid.powers r) (scalarLocalizeMk R r M) :=
  IsLocalizedModule.of_linearEquiv (Submonoid.powers r)
    (M.localizedModuleMkLinearMap (Submonoid.powers r)) (scalarLocalizeEquiv R r M)

/-- Maps out of the actual scalar-localized module are determined by their original numerators. -/
lemma scalarLocalize_hom_ext (R : CommRingCat.{u}) (r : R) {M N : ModuleCat.{u} R}
    {f g : (scalarLocalize R r).obj M ⟶ N}
    (hN : ∀ x : Submonoid.powers r, IsUnit ((algebraMap R (Module.End R N)) x))
    (h : ∀ x, f (scalarLocalizeMk R r M x) = g (scalarLocalizeMk R r M x)) : f = g := by
  apply ModuleCat.hom_ext
  exact IsLocalizedModule.ext (Submonoid.powers r) (scalarLocalizeMk R r M) hN
    (LinearMap.ext h)

/-- The original R-linear restriction of sections. -/
def affineSectionsRestriction (R : CommRingCat.{u}) {U V : (Spec R).Opens} (h : U ≤ V) :
    affineSectionsAt R V ⟶ affineSectionsAt R U where
  app M := (modulesSpecToSheaf.obj M).obj.map (homOfLE h).op
  naturality {_ _} f := ((modulesSpecToSheaf.map f).hom.naturality _).symm

/-- Every power of r acts invertibly on the actual intersection sections. -/
lemma sectionsIntersection_units (R : CommRingCat.{u}) (r : R) (V : (Spec R).Opens)
    (M : (Spec R).Modules) :
    ∀ x : Submonoid.powers r, IsUnit ((algebraMap R
      (Module.End R ((affineSectionsAt R (V ⊓ PrimeSpectrum.basicOpen r)).obj M))) x) := by
  rw [Subtype.forall]
  change Submonoid.powers r ≤ (IsUnit.submonoid _).comap _
  simp only [Submonoid.powers_le, Submonoid.mem_comap]
  exact M.isUnit_algebraMap_end_of_le_basicOpen r inf_le_right

/-- The unique actual localization lift of restriction on arbitrary open sections. -/
def sectionsLocalizationLift (R : CommRingCat.{u}) (r : R) (V : (Spec R).Opens)
    (M : (Spec R).Modules) :
    (scalarLocalize R r).obj ((affineSectionsAt R V).obj M) ⟶
      (affineSectionsAt R (V ⊓ PrimeSpectrum.basicOpen r)).obj M := by
  let N : ModuleCat.{u} R := (affineSectionsAt R (V ⊓ PrimeSpectrum.basicOpen r)).obj M
  let g : ((affineSectionsAt R V).obj M) →ₗ[R] N :=
    ((affineSectionsRestriction R (inf_le_left : V ⊓ PrimeSpectrum.basicOpen r ≤ V)).app M).hom
  let l := IsLocalizedModule.lift (M'' := N) (Submonoid.powers r)
    (scalarLocalizeMk R r ((affineSectionsAt R V).obj M)) g
    (sectionsIntersection_units R r V M)
  exact ConcreteCategory.ofHom l

@[simp]
lemma sectionsLocalizationLift_mk (R : CommRingCat.{u}) (r : R) (V : (Spec R).Opens)
    (M : (Spec R).Modules) (x : (affineSectionsAt R V).obj M) :
    ConcreteCategory.hom
      (X := (ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).obj
        ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj
          (((TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R)).obj
            (modulesSpecToSheaf.obj M)).obj (op V))))
      (Y := ((TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R)).obj
        (modulesSpecToSheaf.obj M)).obj (op (V ⊓ PrimeSpectrum.basicOpen r)))
      (sectionsLocalizationLift R r V M)
      (@DFunLike.coe
        ((((TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R)).obj
              (modulesSpecToSheaf.obj M)).obj (op V)) →ₗ[R]
          ((ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).obj
              ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj
                (((TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R)).obj
                  (modulesSpecToSheaf.obj M)).obj (op V)))))
        (((TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R)).obj
              (modulesSpecToSheaf.obj M)).obj (op V))
        (fun _ => ((ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).obj
              ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj
                (((TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R)).obj
                  (modulesSpecToSheaf.obj M)).obj (op V)))))
        inferInstance
        (scalarLocalizeMk R r
          (((TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R)).obj
            (modulesSpecToSheaf.obj M)).obj (op V))) x) =
    ((affineSectionsRestriction R (inf_le_left : V ⊓ PrimeSpectrum.basicOpen r ≤ V)).app M) x :=
  IsLocalizedModule.lift_apply (Submonoid.powers r)
    (scalarLocalizeMk R r ((affineSectionsAt R V).obj M))
    ((affineSectionsRestriction R (inf_le_left : V ⊓ PrimeSpectrum.basicOpen r ≤ V)).app M).hom
    (sectionsIntersection_units R r V M) x

lemma scalarLocalize_map_mk (R : CommRingCat.{u}) (r : R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (x : M) :
    (scalarLocalize R r).map f (scalarLocalizeMk R r M x) =
      scalarLocalizeMk R r N (f x) :=
  IsLocalizedModule.map_apply (Submonoid.powers r) (M.localizedModuleMkLinearMap _)
    (N.localizedModuleMkLinearMap _) f.hom x

/-- Naturality in the original module sheaf is proved by the localization universal property. -/
lemma sectionsLocalizationLift_naturality (R : CommRingCat.{u}) (r : R) (V : (Spec R).Opens)
    {M N : (Spec R).Modules} (f : M ⟶ N) :
    (scalarLocalize R r).map ((affineSectionsAt R V).map f) ≫ sectionsLocalizationLift R r V N =
      sectionsLocalizationLift R r V M ≫ (affineSectionsAt R (V ⊓ PrimeSpectrum.basicOpen r)).map f
        := by
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext (Submonoid.powers r)
    (scalarLocalizeMk R r ((affineSectionsAt R V).obj M))
    (sectionsIntersection_units R r V N)
  ext x
  change sectionsLocalizationLift R r V N
      ((scalarLocalize R r).map ((affineSectionsAt R V).map f)
        (scalarLocalizeMk R r ((affineSectionsAt R V).obj M) x)) =
    ((affineSectionsAt R (V ⊓ PrimeSpectrum.basicOpen r)).map f)
      (sectionsLocalizationLift R r V M
        (scalarLocalizeMk R r ((affineSectionsAt R V).obj M) x))
  rw [scalarLocalize_map_mk]
  simp only [Functor.comp_obj, evaluation_obj_obj]
  erw [sectionsLocalizationLift_mk, sectionsLocalizationLift_mk]
  exact ConcreteCategory.congr_hom
    ((affineSectionsRestriction R (inf_le_left : V ⊓ PrimeSpectrum.basicOpen r ≤ V)).naturality f) x

/-- Natural actual localization comparison for arbitrary opens, before any cohomological hypotheses.
-/
def sectionsLocalizationComparison (R : CommRingCat.{u}) (r : R) (V : (Spec R).Opens) :
    affineSectionsAt R V ⋙ scalarLocalize R r ⟶
      affineSectionsAt R (V ⊓ PrimeSpectrum.basicOpen r) where
  app := sectionsLocalizationLift R r V
  naturality {_ _} f := sectionsLocalizationLift_naturality R r V f

/-- Shrinking the original open gives a strictly commuting square of localization lifts. -/
lemma sectionsLocalizationLift_restrict (R : CommRingCat.{u}) (r : R)
    {U V : (Spec R).Opens} (h : U ≤ V) (M : (Spec R).Modules) :
    (scalarLocalize R r).map ((affineSectionsRestriction R h).app M) ≫
        sectionsLocalizationLift R r U M =
      sectionsLocalizationLift R r V M ≫
        (affineSectionsRestriction R (inf_le_inf h le_rfl)).app M := by
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext (Submonoid.powers r)
    (scalarLocalizeMk R r ((affineSectionsAt R V).obj M))
    (sectionsIntersection_units R r U M)
  ext x
  change sectionsLocalizationLift R r U M
      ((scalarLocalize R r).map ((affineSectionsRestriction R h).app M)
        (scalarLocalizeMk R r ((affineSectionsAt R V).obj M) x)) =
    ((affineSectionsRestriction R (inf_le_inf h le_rfl)).app M)
      (sectionsLocalizationLift R r V M
        (scalarLocalizeMk R r ((affineSectionsAt R V).obj M) x))
  rw [scalarLocalize_map_mk]
  simp only [Functor.comp_obj, evaluation_obj_obj]
  erw [sectionsLocalizationLift_mk, sectionsLocalizationLift_mk]
  change ((modulesSpecToSheaf.obj M).obj.map _)
      (((modulesSpecToSheaf.obj M).obj.map _) x) =
    ((modulesSpecToSheaf.obj M).obj.map _)
      (((modulesSpecToSheaf.obj M).obj.map _) x)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The actual localization numerator as a natural transformation of R-module functors. -/
def scalarLocalizeUnit (R : CommRingCat.{u}) (r : R) : 𝟭 (ModuleCat.{u} R) ⟶ scalarLocalize R r
  where
  app M := ConcreteCategory.ofHom (scalarLocalizeMk R r M)
  naturality {M N} f := by
    ext x
    exact (scalarLocalize_map_mk R r f x).symm

/-- Original R-module sections of an actual affine module-sheaf complex. -/
abbrev affineSectionsComplex (R : CommRingCat.{u}) (V : (Spec R).Opens)
    (I : CochainComplex (Spec R).Modules ℤ) := ((affineSectionsAt R V).mapHomologicalComplex
      (.up ℤ)).obj I

/-- Actual restriction on section complexes. -/
def affineSectionsComplexRestriction (R : CommRingCat.{u}) {U V : (Spec R).Opens} (h : U ≤ V)
    (I : CochainComplex (Spec R).Modules ℤ) : affineSectionsComplex R V I
      ⟶ affineSectionsComplex R U I :=
  (NatTrans.mapHomologicalComplex (affineSectionsRestriction R h) (.up ℤ)).app I

/-- The genuine localized section comparison, defined for every original open and complex. -/
def sectionsLocalizationComplexComparison (R : CommRingCat.{u}) (r : R) (V : (Spec R).Opens)
    (I : CochainComplex (Spec R).Modules ℤ) :
    ((scalarLocalize R r).mapHomologicalComplex (.up ℤ)).obj (affineSectionsComplex R V I) ⟶
      affineSectionsComplex R (V ⊓ PrimeSpectrum.basicOpen r) I :=
  (NatTrans.mapHomologicalComplex (sectionsLocalizationComparison R r V) (.up ℤ)).app I

/-- The comparison factors the literal original section restriction through the actual
localization numerator chain map. -/
lemma sectionsLocalizationComplexComparison_unit (R : CommRingCat.{u}) (r : R)
    (V : (Spec R).Opens) (I : CochainComplex (Spec R).Modules ℤ) :
    (NatTrans.mapHomologicalComplex (scalarLocalizeUnit R r) (.up ℤ)).app
        (affineSectionsComplex R V I) ≫ sectionsLocalizationComplexComparison R r V I =
      affineSectionsComplexRestriction R (inf_le_left : V ⊓ PrimeSpectrum.basicOpen r ≤ V) I := by
  ext n x
  exact sectionsLocalizationLift_mk R r V (I.X n) x

/-- The original comparison square commutes strictly under every shrinking of opens. -/
lemma sectionsLocalizationComplexComparison_restrict (R : CommRingCat.{u}) (r : R)
    {U V : (Spec R).Opens} (h : U ≤ V) (I : CochainComplex (Spec R).Modules ℤ) :
    ((scalarLocalize R r).mapHomologicalComplex (.up ℤ)).map
        (affineSectionsComplexRestriction R h I) ≫
      sectionsLocalizationComplexComparison R r U I =
    sectionsLocalizationComplexComparison R r V I ≫
      affineSectionsComplexRestriction R (inf_le_inf h le_rfl) I := by
  ext n : 1
  exact sectionsLocalizationLift_restrict R r h (I.X n)

/-- At the ambient affine open, the universal localization lift is the already proved
literal affine principal comparison, up to the original top-intersection identity. -/
lemma sectionsLocalizationComparison_top (R : CommRingCat.{u}) (r : R) :
    sectionsLocalizationComparison R r ⊤ ≫
      (affineSectionsAtCongr R (top_inf_eq (PrimeSpectrum.basicOpen r))).hom =
        principalSectionsScalarComparison R r := by
  apply NatTrans.ext
  funext M
  apply scalarLocalize_hom_ext R r (M := moduleSpecΓFunctor.obj M)
    (show ∀ x : Submonoid.powers r, IsUnit ((algebraMap R
      (Module.End R ((affineSectionsAt R (PrimeSpectrum.basicOpen r)).obj M))) x) by
      rw [Subtype.forall]
      change Submonoid.powers r ≤ (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap]
      exact M.isUnit_algebraMap_end_of_le_basicOpen r le_rfl)
  intro x
  change ((modulesSpecToSheaf.obj M).obj.map (eqToHom
      (top_inf_eq (PrimeSpectrum.basicOpen r)).symm).op)
    (sectionsLocalizationLift R r ⊤ M (scalarLocalizeMk R r (moduleSpecΓFunctor.obj M) x)) =
      (principalSectionsScalarComparison R r).app M
        ((moduleSpecΓFunctor.obj M).localizedModuleMkLinearMap (Submonoid.powers r) x)
  erw [sectionsLocalizationLift_mk R r ⊤ M x, principalSectionsScalarComparison_mk R r M x]
  exact ConcreteCategory.congr_hom
    (((modulesSpecToSheaf.obj M).obj.map_comp
      (homOfLE (show ⊤ ⊓ PrimeSpectrum.basicOpen r ≤ ⊤ from inf_le_left)).op
      (eqToHom (top_inf_eq (PrimeSpectrum.basicOpen r)).symm).op).symm) x

/-- The generic original section comparison is weak at the affine top for the proved
lower-bounded injective QC-homology input. -/
lemma quasiIso_sectionsLocalizationComplexComparison_top {R : CommRingCat.{u}} (r : R)
    (I : CochainComplex (Spec R).Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) :
    QuasiIso (sectionsLocalizationComplexComparison R r ⊤ I) := by
  let e := (NatIso.mapHomologicalComplex
    (affineSectionsAtCongr R (top_inf_eq (PrimeSpectrum.basicOpen r))) (.up ℤ)).app I
  have he : sectionsLocalizationComplexComparison R r ⊤ I ≫ e.hom =
      principalSectionsScalarComplexComparison R r I := by
    ext n : 1
    exact congrArg (fun t => t.app (I.X n)) (sectionsLocalizationComparison_top R r)
  rw [← quasiIso_iff_comp_right _ e.hom, he]
  exact quasiIso_principalSectionsScalarComplexComparison r I a hbound hinj hqc

end Quillen.PerfectComplexes.Affine
