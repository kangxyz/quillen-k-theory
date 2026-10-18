/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.UniverseComparison
public import Quillen.AlgebraicGeometry.Scheme.FlatPullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Original affine coherent pullback and native module localization

For a Noetherian commutative ring and any multiplicative subset, the original
public flat pullback on coherent G-theory agrees with native finite-module
localization under `publicSpecGRingEquiv`, in every degree including zero.

The ordinary comparison first uses the actual coherent sheaf's tilde counit
and Aglib's original affine pullback comparison. Extension of scalars then
compares with the original module-localization functor by its base-change
universal property. Natural-isomorphism invariance gives the lower-model
square, and the accepted comparison between two small models of the same
coherent category gives the public square. No module-carrier universe changes.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent

attribute [local instance] Abelian.hasFiniteBiproducts

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- The actual tilde counit is invertible on the original affine coherent category. -/
def coherentTildeCounitIso :
    (finiteTypeSheavesToModules (Spec R) ⋙ moduleSpecΓFunctor (R := R)) ⋙ tilde.functor R ≅
      finiteTypeSheavesToModules (Spec R) :=
  NatIso.ofComponents (fun M => by
    haveI : M.obj.IsQuasicoherent := coherent_obj_quasicoherent M
    haveI := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M.obj
    exact asIso (Scheme.Modules.fromTildeΓ (R := R) M.obj)) (fun f =>
    (fromTildeΓNatTrans (R := R)).naturality f.hom)

variable {R} {T : CommRingCat.{u}} [IsNoetherianRing T] (φ : R ⟶ T)

/-- Original coherent pullback identifies its actual sections with scalar extension. -/
def coherentPullbackGlobalSectionsExtensionIso :
    coherentPullback (Spec.map φ) ⋙ (globalSectionsExact T).toFunctor ⋙
        forget₂ (FGModuleCat T) (ModuleCat T) ≅
      (globalSectionsExact R).toFunctor ⋙ forget₂ (FGModuleCat R) (ModuleCat R) ⋙
        ModuleCat.extendScalars φ.hom := by
  let Γ := (globalSectionsExact R).toFunctor ⋙ forget₂ (FGModuleCat R) (ModuleCat R)
  let e₁ : Γ ⋙ tilde.functor R ≅ finiteTypeSheavesToModules (Spec R) :=
    coherentTildeCounitIso R
  let e₂ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft Γ (tildePullbackIso φ)) (moduleSpecΓFunctor (R := T))
  let e₃ := Functor.isoWhiskerLeft (Γ ⋙ ModuleCat.extendScalars φ.hom)
    (tilde.toTildeΓNatIso (R := T)).symm
  exact Functor.isoWhiskerRight e₁.symm
      (Scheme.Modules.pullback (Spec.map φ) ⋙ moduleSpecΓFunctor (R := T)) ≪≫ e₂ ≪≫ e₃

end AlgebraicGeometry.Scheme.Modules.Coherent

namespace ModuleCat

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- Native extension of scalars identifies with the original localized module. -/
def scalarLocalizationIso (M : ModuleCat.{u} R) :
    (extendScalars (algebraMap R (Localization S))).obj M ≅ M.localizedModule S :=
  extendScalarsAlgebraObjIso R (Localization S) M ≪≫
    (IsLocalizedModule.isBaseChange S (Localization S)
      (M.localizedModuleMkLinearMap S)).equiv.toModuleIso

open scoped TensorProduct ChangeOfRings

private theorem scalarLocalizationIso_hom_tmul_one (M : ModuleCat.{u} R) (m : M) :
    (scalarLocalizationIso S M).hom ((1 : Localization S) ⊗ₜ[R,algebraMap R (Localization S)] m) =
      M.localizedModuleMkLinearMap S m := by
  change (IsLocalizedModule.isBaseChange S (Localization S)
    (M.localizedModuleMkLinearMap S)).equiv
      ((extendScalarsAlgebraObjIso R (Localization S) M).hom
        ((1 : Localization S) ⊗ₜ[R,algebraMap R (Localization S)] m)) = _
  rw [extendScalarsAlgebraObjIso_hom_tmul, IsBaseChange.equiv_tmul, one_smul]

/-- The native scalar-extension and module-localization comparisons are natural. -/
def extendScalarsLocalizationIso :
    extendScalars (algebraMap R (Localization S)) ≅ localizedModuleFunctor S :=
  NatIso.ofComponents (scalarLocalizationIso S) (fun {M N} f => by
    apply ExtendScalars.hom_ext
    intro m
    change (scalarLocalizationIso S N).hom
        ((extendScalars (algebraMap R (Localization S))).map f
          ((1 : Localization S) ⊗ₜ[R,algebraMap R (Localization S)] m)) =
      localizedModuleMap S f ((scalarLocalizationIso S M).hom
        ((1 : Localization S) ⊗ₜ[R,algebraMap R (Localization S)] m))
    rw [ExtendScalars.map_tmul, scalarLocalizationIso_hom_tmul_one,
      scalarLocalizationIso_hom_tmul_one]
    exact (IsLocalizedModule.map_apply S (M.localizedModuleMkLinearMap S)
      (N.localizedModuleMkLinearMap S) f.hom m).symm)

end ModuleCat

namespace AlgebraicGeometry.Scheme.Modules.Coherent

attribute [local instance] Abelian.hasFiniteBiproducts

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (S : Submonoid R)

/-- The actual spectrum map of a ring localization is flat. -/
instance localizationSpecMap_flat :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization S) S))

/-- Actual affine coherent pullback and actual global sections commute with module localization. -/
def coherentLocalizationGlobalSectionsIso :
    ((coherentExactPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))).comp
        (globalSectionsExact (CommRingCat.of (Localization S)))).toFunctor ≅
      ((globalSectionsExact (CommRingCat.of R)).comp
        (Quillen.FiniteModuleLocalization.exactFunctor S)).toFunctor := by
  apply Functor.fullyFaithfulCancelRight
    (forget₂ (FGModuleCat (Localization S)) (ModuleCat (Localization S)))
  exact coherentPullbackGlobalSectionsExtensionIso
      (CommRingCat.ofHom (algebraMap R (Localization S))) ≪≫
    Functor.isoWhiskerLeft
      ((globalSectionsExact (CommRingCat.of R)).toFunctor ⋙
        forget₂ (FGModuleCat R) (ModuleCat R))
      (ModuleCat.extendScalarsLocalizationIso S)

/-- The original lower-model pullback K-map retains native finite-module localization. -/
theorem lowerPullbackG_globalSections_localization (n : ℕ) :
    ((globalSectionsExact (CommRingCat.of (Localization S))).smallKMap.{u} n).comp
      ((coherentExactPullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))).smallKMap.{u} n) =
    (Quillen.FiniteModuleLocalization.localizationKMap S n).comp
      ((globalSectionsExact (CommRingCat.of R)).smallKMap.{u} n) := by
  have h := ExactFunctor.smallKMap_eq_of_natIso.{u}
    (F := (coherentExactPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))).comp
        (globalSectionsExact (CommRingCat.of (Localization S))))
    (G := (globalSectionsExact (CommRingCat.of R)).comp
      (Quillen.FiniteModuleLocalization.exactFunctor S))
    (coherentLocalizationGlobalSectionsIso S) n
  simpa only [ExactFunctor.smallKMap_comp,
    Quillen.FiniteModuleLocalization.localizationKMap] using h

/-- The original public flat pullback agrees with native localization in every G-degree. -/
theorem publicSpecGRingEquiv_localization_pullback (n : ℕ) :
    (publicSpecGRingEquiv (CommRingCat.of (Localization S)) n).toMonoidHom.comp
      (Scheme.pullbackG
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) n) =
    (Quillen.FiniteModuleLocalization.localizationKMap S n).comp
      (publicSpecGRingEquiv (CommRingCat.of R) n).toMonoidHom := by
  let F := coherentExactPullback
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))
  have hn := ExactFunctor.smallKUniverseEquiv_naturality.{u+1,u} F n
  ext a
  change specGRingEquiv (CommRingCat.of (Localization S)) n
      ((coherentExactStructure (Spec (CommRingCat.of (Localization S)))).smallKUniverseEquiv.{u+1,u}
        n (Scheme.pullbackG
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) n a)) =
    Quillen.FiniteModuleLocalization.localizationKMap S n
      (specGRingEquiv (CommRingCat.of R) n
        ((coherentExactStructure (Spec (CommRingCat.of R))).smallKUniverseEquiv.{u+1,u} n a))
  have ht := DFunLike.congr_fun
    (specGRingEquiv_eq_globalSectionsKMap (CommRingCat.of (Localization S)) n)
    ((coherentExactStructure (Spec (CommRingCat.of (Localization S)))).smallKUniverseEquiv.{u+1,u}
      n (Scheme.pullbackG
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) n a))
  have hr := DFunLike.congr_fun
    (specGRingEquiv_eq_globalSectionsKMap (CommRingCat.of R) n)
    ((coherentExactStructure (Spec (CommRingCat.of R))).smallKUniverseEquiv.{u+1,u} n a)
  change specGRingEquiv (CommRingCat.of (Localization S)) n _ = _ at ht
  change specGRingEquiv (CommRingCat.of R) n _ = _ at hr
  rw [ht, hr]
  exact (congrArg ((globalSectionsExact (CommRingCat.of (Localization S))).smallKMap.{u} n)
    (DFunLike.congr_fun hn a).symm).trans
      (DFunLike.congr_fun (lowerPullbackG_globalSections_localization S n)
        ((coherentExactStructure (Spec (CommRingCat.of R))).smallKUniverseEquiv.{u+1,u} n a))

end AlgebraicGeometry.Scheme.Modules.Coherent
