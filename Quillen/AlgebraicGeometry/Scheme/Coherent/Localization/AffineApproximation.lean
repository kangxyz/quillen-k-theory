/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Localization.FiniteApproximation
public import Aglib.AlgebraicGeometry.Modules.Locality.Isomorphisms
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison

/-!
# Finite coherent approximation on a compact affine open

Finite submodules capture finite restrictions of a quasicoherent affine
sheaf on finitely many principal opens. The resulting inclusion is checked
on actual sheaf restriction maps, using the natural localization comparison.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Global sections reflect isomorphisms between actual quasicoherent
sheaves on an affine scheme. -/
theorem affine_isIso_of_globalSections (R : CommRingCat.{u})
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [IsIso (moduleSpecΓFunctor.map f)] : IsIso f := by
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  have he : (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f := Scheme.Modules.fromTildeΓNatTrans.naturality f
  rw [← isIso_comp_left_iff M.fromTildeΓ f, ← he]
  infer_instance

/-- A finite submodule whose localization is the whole localized module has
an isomorphic localized inclusion. -/
theorem isIso_localized_subtype_of_eq_top (R : CommRingCat.{u}) (p : Submonoid R)
    (M : ModuleCat.{u} R) (L : Submodule R M)
    (hL : L.localized' (Localization p) p (M.localizedModuleMkLinearMap p) = ⊤) :
    IsIso (ModuleCat.localizedModuleMap p (ModuleCat.ofHom L.subtype)) := by
  let a : ModuleCat.of.{u} R L ⟶ M := ModuleCat.ofHom L.subtype
  have : Mono a := (ModuleCat.mono_iff_injective a).mpr Subtype.val_injective
  have : Mono (ModuleCat.localizedModuleMap p a) :=
    (ModuleCat.localizedModuleFunctor p).map_mono a
  have hloc : IsLocalizedModule p ((ModuleCat.of.{u} R L).localizedModuleMkLinearMap p) :=
    ModuleCat.localizedModule_isLocalizedModule _ _
  have : Epi (ModuleCat.localizedModuleMap p a) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    apply LinearMap.range_eq_top.mp
    change LinearMap.range (IsLocalizedModule.mapExtendScalars p
      ((ModuleCat.of.{u} R L).localizedModuleMkLinearMap p)
      (M.localizedModuleMkLinearMap p) (Localization p) L.subtype) = ⊤
    change LinearMap.range ((IsLocalizedModule.map p
      ((ModuleCat.of.{u} R L).localizedModuleMkLinearMap p)
      (M.localizedModuleMkLinearMap p) L.subtype).extendScalarsOfIsLocalization p
        (Localization p)) = ⊤
    rw [← LinearMap.localized'_range_eq_range_localizedMap (Localization p) p
      ((ModuleCat.of.{u} R L).localizedModuleMkLinearMap p) (M.localizedModuleMkLinearMap p)]
    simpa only [a, ModuleCat.hom_ofHom, Submodule.range_subtype] using hL
  exact isIso_of_mono_of_epi _

/-- One finitely generated submodule captures all finite restrictions on a
finite family of principal affine opens, with actual sheaf isomorphisms. -/
theorem exists_fg_submodule_principal_restriction_isIso
    (R : CommRingCat.{u}) (M : ModuleCat.{u} R) {ι : Type v} [Finite ι]
    (r : ι → R) [∀ i, Module.Finite (Localization.Away (r i))
      (restrictionGlobalSections R (r i) M)] :
    ∃ L : Submodule R M, L.FG ∧ ∀ i,
      IsIso ((Scheme.Modules.restrictFunctor (principalOpen R (r i))).map
        (tilde.map (ModuleCat.ofHom L.subtype))) := by
  have hfin (i : ι) : Module.Finite (Localization.Away (r i))
      (M.localizedModule (.powers (r i))) :=
    Module.Finite.of_surjective (localizationRestrictionIso R (r i) M).inv.hom
      (ConcreteCategory.bijective_of_isIso _).surjective
  obtain ⟨L, hL, htop⟩ := exists_fg_submodule_localized_eq_top_finite
    (fun i => Submonoid.powers (r i)) (fun i => Localization.Away (r i))
    (fun i => M.localizedModule (.powers (r i)))
    (fun i => M.localizedModuleMkLinearMap (.powers (r i)))
  refine ⟨L, hL, fun i => ?_⟩
  have hlociso : IsIso (ModuleCat.localizedModuleMap (.powers (r i)) (ModuleCat.ofHom L.subtype)) :=
    isIso_localized_subtype_of_eq_top R _ M L (htop i)
  have hΓ : IsIso ((restrictionGlobalSectionsFunctor R (r i)).map (ModuleCat.ofHom L.subtype)) :=
    (NatIso.isIso_map_iff (localizationRestrictionNatIso R (r i)) _).mp hlociso
  have : IsIso (moduleSpecΓFunctor.map
      ((Scheme.Modules.restrictFunctor (principalOpen R (r i))).map
        (tilde.map (ModuleCat.ofHom L.subtype)))) := hΓ
  exact affine_isIso_of_globalSections _ _

/-- Coherence on an arbitrary compact open of an affine scheme is already
captured by a finite submodule of the global module. The equality on the
open is an isomorphism of actual sheaves. -/
theorem exists_fg_submodule_open_restriction_isIso
    (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (V : (Spec R).Opens)
    (hV : IsCompact (V : Set (Spec R)))
    (hM : affineLocallyFiniteType V.toScheme ((tilde M).restrict V.ι)) :
    ∃ L : Submodule R M, L.FG ∧
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map
        (tilde.map (ModuleCat.ofHom L.subtype))) := by
  classical
  obtain ⟨ι, _, r, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact V hV
  have hle (i : ι) : PrimeSpectrum.basicOpen (r i) ≤ V := by
    rw [hr]
    exact le_iSup_of_le _ le_rfl
  have hfin (i : ι) : Module.Finite (Localization.Away (r i))
      (restrictionGlobalSections R (r i) M) := by
    let t := (Spec R).homOfLE (U := PrimeSpectrum.basicOpen (r i)) (V := V) (hle i)
    let q := (basicOpenIsoSpecAway (r i)).inv ≫ t
    let e : Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.restrictFunctor q ≅
        Scheme.Modules.restrictFunctor (principalOpen R (r i)) :=
      (Scheme.Modules.restrictFunctorComp q V.ι).symm ≪≫
        Scheme.Modules.restrictFunctorCongr (by simp [q, t, basicOpenIsoSpecAway])
    exact ((affineFiniteSheaf (CommRingCat.of (Localization.Away (r i)))).prop_of_iso
      (e.app (tilde M)) (hM _ q)).2
  obtain ⟨L, hL, hLi⟩ := exists_fg_submodule_principal_restriction_isIso R M r
  refine ⟨L, hL, ?_⟩
  apply moduleSheaf_isIso_restrict_of_openCover V.ι
    (fun i => Spec (CommRingCat.of (Localization.Away (r i))))
    (fun i => principalOpen R (r i)) ?_ _ hLi
  intro x
  have hx : (x.1 : Spec R) ∈ ⨆ i, PrimeSpectrum.basicOpen (r i) := by
    rw [← hr]
    exact x.2
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hi' : V.ι x ∈ (principalOpen R (r i)).opensRange := by
    rw [Scheme.Hom.opensRange_localizationAway]
    exact hi
  exact ⟨i, hi'⟩

/-- Over an arbitrary commutative ring, a quasicoherent affine sheaf of finite type on a
compact open contains an affine-local finite-type subsheaf agreeing on that open.
The construction uses a finitely generated global submodule and needs no noetherian hypothesis. -/
theorem exists_coherent_subsheaf_restrict_isIso
    (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [M.IsQuasicoherent] (V : (Spec R).Opens) (hV : IsCompact (V : Set (Spec R)))
    (hM : affineLocallyFiniteType V.toScheme (M.restrict V.ι)) :
    ∃ (N : FiniteTypeSheaves (Spec R)) (i : N.obj ⟶ M), Mono i ∧
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map i) := by
  let P := moduleSpecΓFunctor.obj M
  let : Module R P := P.isModule
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let e : tilde P ≅ M := asIso M.fromTildeΓ
  have hP : affineLocallyFiniteType V.toScheme ((tilde P).restrict V.ι) :=
    (affineLocallyFiniteType V.toScheme).prop_of_iso
      ((Scheme.Modules.restrictFunctor V.ι).mapIso e.symm) hM
  obtain ⟨L, hL, hi⟩ := exists_fg_submodule_open_restriction_isIso R P V hV hP
  have : Module.Finite R L := Module.Finite.of_fg hL
  let N : FiniteTypeSheaves (Spec R) :=
    ⟨tilde (ModuleCat.of.{u} R L), (affineLocallyFiniteType_spec_iff R _).mpr
      ⟨inferInstance, by
        have : Module.Finite R (ModuleCat.of.{u} R L) := inferInstanceAs (Module.Finite R L)
        let eL : ModuleCat.of.{u} R L ≅ moduleSpecΓFunctor.obj (tilde (ModuleCat.of.{u} R L)) :=
          tilde.toTildeΓNatIso.app (ModuleCat.of.{u} R L)
        exact Module.Finite.equiv eL.toLinearEquiv⟩⟩
  let a : ModuleCat.of.{u} R L ⟶ P := ModuleCat.ofHom (Y := P) L.subtype
  have : Mono a := (ModuleCat.mono_iff_injective a).mpr (by
    intro x y h
    exact Subtype.ext h)
  have : Mono (tilde.map a) := (tilde.functor R).map_mono a
  let i : N.obj ⟶ M := tilde.map a ≫ e.hom
  refine ⟨N, i, ?_, ?_⟩
  · dsimp only [i]
    infer_instance
  · dsimp only [i]
    rw [Functor.map_comp]
    have : IsIso ((Scheme.Modules.restrictFunctor V.ι).map (tilde.map a)) := hi
    infer_instance

end AlgebraicGeometry.Scheme.Modules.Coherent
