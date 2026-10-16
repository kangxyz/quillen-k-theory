/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Category.FGModuleCat.ClosedSupportSmallModel

public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Quillen.Devissage.CentralEndomorphism
public import Quillen.Aglib.Algebra.Category.FGModuleCat.PrincipalClosedSupport

/-!
# Principal closed pushforward and G-theory dévissage

The comparison is induced by actual quotient-ring restriction of scalars.
The finite-module quotient equivalence is used only for modules killed by f;
its passage to all supported modules is the proved image-filtration dévissage.
-/
@[expose] public section

open CategoryTheory.ExactCategory


open ModuleCat

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.FiniteModuleLocalization
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R)

instance smallClosedToKilledExact_mapQ_isEquivalence :
    (smallClosedToKilledExact f).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N a ha
    rw [show (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing f)).smallModel =
      abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} (ClosedRing f))) from
      abelianExactStructure_smallModel _]
    rw [abelianExactStructure_inflation_iff]
    have : Mono ((smallClosedToKilled f).map a) := (abelianExactStructure_inflation_iff _ _).1 ha
    exact Functor.mono_of_mono_map (smallClosedToKilled f) this
  · intro M N a ha
    rw [show (ModuleCat.finiteModuleExactStructure.{u, u} (ClosedRing f)).smallModel =
      abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} (ClosedRing f))) from
      abelianExactStructure_smallModel _]
    rw [abelianExactStructure_deflation_iff]
    have : Epi ((smallClosedToKilled f).map a) := (abelianExactStructure_deflation_iff _ _).1 ha
    exact Functor.epi_of_epi_map (smallClosedToKilled f) this

/-- G-theory of the principal closed subscheme is isomorphic to supported G-theory. -/
def closedSupportGEquiv (n : ℕ) : G (ClosedRing f) n ≃* SupportedG (Submonoid.powers f) n :=
  ((smallClosedToKilledExact f).KEquivOfMapQIsEquivalence n).trans
    (principalDevissageKEquiv f n)

/-- The canonical closed-to-supported map, induced by actual restriction of scalars. -/
def closedSupportedKMap (n : ℕ) : G (ClosedRing f) n →* SupportedG (Submonoid.powers f) n :=
  (smallClosedToSupportExact f).KMap n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem closedSupportGEquiv_coe (n : ℕ) :
    ↑(closedSupportGEquiv f n) = closedSupportedKMap f n := by
  rw [closedSupportedKMap, smallClosedToSupportExact,
    CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
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
  have h : ((smallClosedToKilledExact f).comp (CategoryTheory.ObjectProperty.exactInclusion
    (principalKilled f))).comp
      (CategoryTheory.ObjectProperty.exactInclusion (smallTorsion (Submonoid.powers f))) =
    (closedRestrictionExact f).smallModel.comp (smallModelToAbelian R) := by rfl
  have hk := congrArg (fun F ↦ F.KMap n) h
  simp only [CategoryTheory.ExactCategory.ExactFunctor.KMap_comp] at hk
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
