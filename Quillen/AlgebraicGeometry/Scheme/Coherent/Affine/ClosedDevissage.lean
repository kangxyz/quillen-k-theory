/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Devissage.CentralEndomorphism
public import Quillen.GTheory.FiniteModules.ClosedSupport

/-!
# Principal closed pushforward and G-theory dévissage

The comparison is induced by actual quotient-ring restriction of scalars.
The finite-module quotient equivalence is used only for modules killed by f;
its passage to all supported modules is the proved image-filtration dévissage.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.FiniteModuleLocalization
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R)

omit [IsNoetherianRing R] in
lemma killedBy_of_iso {M N : FGModuleCat.{u} R} (e : M ≅ N) (hM : killedBy f M) :
    killedBy f N := by
  intro n
  obtain ⟨m, rfl⟩ := (FGModuleCat.isoToLinearEquiv e).surjective n
  rw [← map_smul, hM m, map_zero]

/-- The canonical small-model quotient-ring restriction, with no changed choices. -/
abbrev smallClosedFunctor := (closedRestrictionExact f).smallModel.toFunctor

lemma smallClosedFunctor_killed (M : SmallModel.{u} (FGModuleCat.{u} (ClosedRing f))) :
    killedBy f ((equivSmallModel (FGModuleCat.{u} R)).inverse.obj
      ((smallClosedFunctor f).obj M)) := by
  apply killedBy_of_iso f
    ((equivSmallModel (FGModuleCat.{u} R)).unitIso.app
      ((closedRestriction f).obj ((equivSmallModel (FGModuleCat.{u} (ClosedRing f))).inverse.obj
        M)))
  exact closedRestriction_killed f _

/-- The actual closed pushforward lands in modules supported on V(f). -/
def smallClosedToSupport : SmallModel.{u} (FGModuleCat.{u} (ClosedRing f)) ⥤ PrincipalSupport f :=
  ObjectProperty.lift _ (smallClosedFunctor f) (fun M ↦ by
    rw [smallTorsion_powers_iff_uniform]
    refine ⟨1, ?_⟩
    intro m
    simpa only [pow_one] using smallClosedFunctor_killed f M m)

/-- Its further factorization lands exactly in the killed-by-f objects. -/
def smallClosedToKilled : SmallModel.{u} (FGModuleCat.{u} (ClosedRing f)) ⥤
    (principalKilled f).FullSubcategory :=
  ObjectProperty.lift _ (smallClosedToSupport f) (fun M ↦
    (principalKilled_iff f _).2 (smallClosedFunctor_killed f M))

instance smallClosedFunctor_full : (smallClosedFunctor f).Full := by
  change (((equivSmallModel (FGModuleCat.{u} (ClosedRing f))).inverse ⋙
    closedRestriction f) ⋙ (equivSmallModel (FGModuleCat.{u} R)).functor).Full
  infer_instance

instance smallClosedFunctor_faithful : (smallClosedFunctor f).Faithful := by
  change (((equivSmallModel (FGModuleCat.{u} (ClosedRing f))).inverse ⋙
    closedRestriction f) ⋙ (equivSmallModel (FGModuleCat.{u} R)).functor).Faithful
  infer_instance

instance smallClosedToKilled_full : (smallClosedToKilled f).Full where
  map_surjective {M N} a := by
    obtain ⟨b, hb⟩ := (smallClosedFunctor f).map_surjective a.hom.hom
    exact ⟨b, ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ hb)⟩

instance smallClosedToKilled_faithful : (smallClosedToKilled f).Faithful where
  map_injective h := (smallClosedFunctor f).map_injective
    (congrArg (fun a ↦ a.hom.hom) h)

/-- Every killed support object comes from an actual finite quotient-ring module. -/
instance smallClosedToKilled_essSurj : (smallClosedToKilled f).EssSurj where
  mem_essImage M := by
    let N : (killedBy f).FullSubcategory :=
      ⟨(principalRepresentation f).obj M.obj, (principalKilled_iff f M.obj).1 M.property⟩
    let L := (closedEquivalence f).inverse.obj N
    let e : (closedRestriction f).obj L ≅ N.obj :=
      (killedBy f).ι.mapIso ((closedEquivalence f).counitIso.app N)
    let Q := (equivSmallModel (FGModuleCat.{u} (ClosedRing f)))
    let A := (equivSmallModel (FGModuleCat.{u} R))
    refine ⟨Q.functor.obj L, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact A.functor.mapIso ((closedRestriction f).mapIso (Q.unitIso.app L).symm ≪≫ e) ≪≫
      A.counitIso.app M.obj.obj

instance smallClosedToKilled_isEquivalence : (smallClosedToKilled f).IsEquivalence := {}

instance smallClosedToKilled_additive : (smallClosedToKilled f).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (smallClosedFunctor f).map_add

/-- The actual small restriction functor is an equivalence onto the killed objects. -/
def smallClosedEquivalence : SmallModel.{u} (FGModuleCat.{u} (ClosedRing f)) ≌
    (principalKilled f).FullSubcategory := (smallClosedToKilled f).asEquivalence

/-- This equivalence uses the original transported exact structure on its source. -/
def smallClosedToKilledExact :
    ExactFunctor (CoherentScheme.finiteModuleExactStructure.{u, u} (ClosedRing f)).smallModel
      (Devissage.subcategoryExactStructure (principalKilled f)) where
  toFunctor := smallClosedToKilled f
  map_conflation S h := by
    rw [show (CoherentScheme.finiteModuleExactStructure.{u, u} (ClosedRing f)).smallModel =
      abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} (ClosedRing f))) from
      abelianExactStructure_smallModel _] at h
    exact h.map_of_exact _

instance smallClosedToKilledExact_isEquivalence :
    (smallClosedToKilledExact f).toFunctor.IsEquivalence := smallClosedToKilled_isEquivalence f

instance smallClosedToKilledExact_mapQ_isEquivalence :
    (smallClosedToKilledExact f).mapQ.IsEquivalence := by
  apply ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N a ha
    rw [show (CoherentScheme.finiteModuleExactStructure.{u, u} (ClosedRing f)).smallModel =
      abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} (ClosedRing f))) from
      abelianExactStructure_smallModel _]
    rw [abelianExactStructure_inflation_iff]
    have : Mono ((smallClosedToKilled f).map a) := (abelianExactStructure_inflation_iff _ _).1 ha
    exact Functor.mono_of_mono_map (smallClosedToKilled f) this
  · intro M N a ha
    rw [show (CoherentScheme.finiteModuleExactStructure.{u, u} (ClosedRing f)).smallModel =
      abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} (ClosedRing f))) from
      abelianExactStructure_smallModel _]
    rw [abelianExactStructure_deflation_iff]
    have : Epi ((smallClosedToKilled f).map a) := (abelianExactStructure_deflation_iff _ _).1 ha
    exact Functor.epi_of_epi_map (smallClosedToKilled f) this

/-- G-theory of the principal closed subscheme is isomorphic to supported G-theory. -/
def closedSupportGEquiv (n : ℕ) : G (ClosedRing f) n ≃* SupportedG (Submonoid.powers f) n :=
  ((smallClosedToKilledExact f).KEquivOfMapQIsEquivalence n).trans
    (principalDevissageKEquiv f n)

/-- Actual closed restriction of scalars with codomain in the supported category. -/
def smallClosedToSupportExact :
    ExactFunctor (CoherentScheme.finiteModuleExactStructure.{u, u} (ClosedRing f)).smallModel
      (Devissage.subcategoryExactStructure (smallTorsion (Submonoid.powers f))) :=
  (smallClosedToKilledExact f).comp (Devissage.exactInclusion (principalKilled f))

/-- The canonical closed-to-supported map, induced by actual restriction of scalars. -/
def closedSupportedKMap (n : ℕ) : G (ClosedRing f) n →* SupportedG (Submonoid.powers f) n :=
  (smallClosedToSupportExact f).KMap n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem closedSupportGEquiv_coe (n : ℕ) :
    ↑(closedSupportGEquiv f n) = closedSupportedKMap f n := by
  rw [closedSupportedKMap, smallClosedToSupportExact, ExactFunctor.KMap_comp]
  rfl

/-- The actual closed-to-supported K-map is bijective in every connective degree. -/
theorem closedSupportedKMap_bijective (n : ℕ) : Function.Bijective (closedSupportedKMap f n) := by
  rw [← closedSupportGEquiv_coe]
  exact (closedSupportGEquiv f n).bijective

/-- The actual pushforward from the principal closed subscheme. -/
def closedPushforwardKMap (n : ℕ) : G (ClosedRing f) n →* G R n :=
  (closedRestrictionExact f).smallKMap n

/-- The dévissage comparison commutes with the original canonical closed
pushforward, including the small-model and zero-object normalizations. -/
theorem closedSupportGEquiv_pushforward (n : ℕ) :
    (supportedKMap (Submonoid.powers f) n).comp (closedSupportGEquiv f n).toMonoidHom =
      closedPushforwardKMap f n := by
  have h : ((smallClosedToKilledExact f).comp (Devissage.exactInclusion (principalKilled f))).comp
      (Devissage.exactInclusion (smallTorsion (Submonoid.powers f))) =
    (closedRestrictionExact f).smallModel.comp (smallModelToAbelian R) := by rfl
  have hk := congrArg (fun F ↦ F.KMap n) h
  simp only [ExactFunctor.KMap_comp] at hk
  ext x
  apply (smallAbelianKEquiv R n).injective
  change smallAbelianKEquiv R n ((smallAbelianKEquiv R n).symm
      (Devissage.KMap (smallTorsion (Submonoid.powers f)) n
        (Devissage.KMap (principalKilled f) n ((smallClosedToKilledExact f).KMap n x)))) = _
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun hk x

/-- The boundary with values in G-theory of the actual principal closed subscheme. -/
def closedConnectingHom (n : ℕ) :
    G (Localization (Submonoid.powers f)) (n + 1) →* G (ClosedRing f) n :=
  (closedSupportGEquiv f n).symm.toMonoidHom.comp (connectingHom (Submonoid.powers f) n)

/-- Exactness at G_n(R), with actual closed pushforward and actual open localization. -/
theorem closedPushforward_range_eq_localization_ker (n : ℕ) :
    (closedPushforwardKMap f n).range = (localizationKMap (Submonoid.powers f) n).ker := by
  rw [← closedSupportGEquiv_pushforward]
  rw [MonoidHom.range_comp]
  rw [MonoidHom.range_eq_top.mpr (closedSupportGEquiv f n).surjective, Subgroup.map_top]
  exact supported_range_eq_localization_ker _ n

/-- Exactness at G_(n+1)(R[f⁻¹]) for the closed-subscheme boundary. -/
theorem localization_range_eq_closedConnecting_ker (n : ℕ) :
    (localizationKMap (Submonoid.powers f) (n + 1)).range = (closedConnectingHom f n).ker := by
  rw [localization_range_eq_connecting_ker]
  ext x
  simp only [MonoidHom.mem_ker, closedConnectingHom, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  constructor
  · intro h; rw [h, map_one]
  · intro h
    apply (closedSupportGEquiv f n).symm.injective
    simpa only [map_one] using h

/-- Exactness at G_n(R/(f)), obtained by the proved canonical dévissage isomorphism. -/
theorem closedConnecting_range_eq_pushforward_ker (n : ℕ) :
    (closedConnectingHom f n).range = (closedPushforwardKMap f n).ker := by
  ext x
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : connectingHom (Submonoid.powers f) n y ∈
        (supportedKMap (Submonoid.powers f) n).ker := by
      rw [← connecting_range_eq_supported_ker]
      exact ⟨y, rfl⟩
    have hx := DFunLike.congr_fun (closedSupportGEquiv_pushforward f n)
      (closedConnectingHom f n y)
    simp only [MonoidHom.comp_apply, closedConnectingHom, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulEquiv.apply_symm_apply] at hx
    exact hx.symm.trans hy
  · intro hx
    have he : closedSupportGEquiv f n x ∈ (supportedKMap (Submonoid.powers f) n).ker := by
      change supportedKMap (Submonoid.powers f) n (closedSupportGEquiv f n x) = 1
      exact (DFunLike.congr_fun (closedSupportGEquiv_pushforward f n) x).trans hx
    rw [← connecting_range_eq_supported_ker] at he
    obtain ⟨y, hy⟩ := he
    refine ⟨y, ?_⟩
    change (closedSupportGEquiv f n).symm (connectingHom (Submonoid.powers f) n y) = x
    rw [hy, MulEquiv.symm_apply_apply]

/-- The genuine principal closed/open connective G-localization sequence,
including its terminal G₀ surjection. -/
theorem principalClosedLocalization_longExact :
    (∀ n, (closedPushforwardKMap f n).range = (localizationKMap (Submonoid.powers f) n).ker) ∧
    (∀ n, (localizationKMap (Submonoid.powers f) (n + 1)).range = (closedConnectingHom f n).ker) ∧
    (∀ n, (closedConnectingHom f n).range = (closedPushforwardKMap f n).ker) ∧
    Function.Surjective (localizationKMap (Submonoid.powers f) 0) :=
  ⟨closedPushforward_range_eq_localization_ker f, localization_range_eq_closedConnecting_ker f,
    closedConnecting_range_eq_pushforward_ker f, localizationKZero_surjective _⟩

end Quillen.FiniteModuleLocalization
