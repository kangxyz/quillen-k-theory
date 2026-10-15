/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.Killed
public import Quillen.AlgebraicGeometry.Scheme.Coherent.PrincipalLocalization
public import Quillen.Devissage.CentralEndomorphism

/-!
# Actual supported coherent sheaves and their principal image filtrations

The compatible upper-universe small category is the actual kernel of
principal-open restriction. Its fully faithful finite-module representation
allows scalar multiplication even though the sheaf category and ring have
different universes. The resulting nilpotent image filtration is genuine
categorical dévissage, not an equivalence with all supported objects.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.CoherentScheme


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
open FiniteModuleLocalization PrincipalSupportDevissage

namespace ScalarRepresentation
variable {C : Type w} [Category.{v} C] [Abelian C]
  {A : Type u} [CommRing A] (F : C ⥤ FGModuleCat.{u} A) [F.Full] [F.Faithful]

/-- Scalar multiplication lifted through a fully faithful representation,
with independent ring and category universes. -/
def scalar (f : A) : 𝟭 C ⟶ 𝟭 C where
  app X := F.preimage (FGModuleCat.ofHom (LinearMap.lsmul A (F.obj X) f))
  naturality {X Y} a := by
    apply F.map_injective
    simp only [Functor.id_map, Functor.map_comp, Functor.map_preimage]
    ext m
    exact ((F.map a).hom.hom.map_smul f m).symm

omit [Abelian C] in
@[simp] theorem map_scalar (f : A) (X : C) :
    F.map ((scalar F f).app X) = FGModuleCat.ofHom (LinearMap.lsmul A (F.obj X) f) :=
  F.map_preimage _

omit [Abelian C] in
theorem map_power_apply (f : A) (X : C) (n : ℕ) (m : F.obj X) :
    (F.map (power (scalar F f) X n)).hom.hom m = f ^ n • m := by
  induction n with
  | zero => simp [power]
  | succ n ih =>
    simp only [power_succ, Functor.map_comp, map_scalar]
    change (F.map (power (scalar F f) X n)).hom.hom (f • m) = f ^ (n + 1) • m
    rw [map_smul, ih, smul_smul, pow_succ']

variable [F.Additive]

theorem killed_iff (f : A) (X : C) :
    killed (scalar F f) X ↔ ∀ m : F.obj X, f • m = 0 := by
  change (scalar F f).app X = 0 ↔ _
  rw [← F.map_injective.eq_iff, map_scalar, F.map_zero]
  constructor
  · intro h m
    exact congrArg (fun a ↦ a.hom.hom m) h
  · intro h
    ext m
    exact h m

theorem power_eq_zero (f : A) (X : C) (n : ℕ)
    (h : ∀ m : F.obj X, f ^ n • m = 0) : power (scalar F f) X n = 0 := by
  apply F.map_injective
  rw [F.map_zero]
  ext m
  exact (map_power_apply F f X n m).trans (h m)
end ScalarRepresentation

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

/-- Geometric vanishing on the principal open is exactly torsion of the
actual global-section module. -/
theorem finiteTypeSheavesSupportedAway_iff_torsion (M : FiniteTypeSheaves (Spec R)) :
    finiteTypeSheavesSupportedAway (principalOpen R f) M ↔
      torsion (Submonoid.powers f) ((finiteTypeSheavesSpecModuleEquivalence R).functor.obj M) := by
  rw [← finiteTypeSheavesRestriction_kernel_eq_support]
  let e := (affinePrincipalRestrictionSquare R f).app
    ((finiteTypeSheavesAffineEquivalence R).functor.obj M)
  change IsZero ((finiteTypeSheavesRestriction (principalOpen R f)).obj M) ↔
    IsZero ((functor (Submonoid.powers f)).obj
      ((finiteTypeSheavesSpecModuleEquivalence R).functor.obj M))
  constructor
  · intro h
    exact ((finiteTypeSheavesSpecModuleEquivalence (CommRingCat.of (Localization.Away
      f))).functor.map_isZero h).of_iso e
  · intro h
    exact IsZero.of_full_of_faithful_of_isZero
      (finiteTypeSheavesSpecModuleEquivalence (CommRingCat.of (Localization.Away f))).functor _
      (h.of_iso e.symm)

/-- A single power of f kills every section of a supported coherent sheaf. -/
theorem finiteTypeSheavesSupportedAway_iff_uniform (M : FiniteTypeSheaves (Spec R)) :
    finiteTypeSheavesSupportedAway (principalOpen R f) M ↔ ∃ n : ℕ,
      ∀ m : (finiteTypeSheavesSpecModuleEquivalence R).functor.obj M, f ^ n • m = 0 := by
  rw [finiteTypeSheavesSupportedAway_iff_torsion, torsion_powers_iff_uniform]

/-- The actual small category used by public principal-open localization. -/
abbrev SmallSupport := (coherentPrincipalSmallSupport R f).FullSubcategory

/-- Actual sheaves represented by the compatible support category, followed
by their actual finite global-section modules. -/
abbrev supportRepresentation : SmallSupport R f ⥤ FGModuleCat.{u} R :=
  (coherentPrincipalSmallSupport R f).ι ⋙
    (equivSmallModel.{u+1} (FiniteTypeSheaves (Spec R))).inverse ⋙
      (finiteTypeSheavesSpecModuleEquivalence R).functor

instance supportRepresentation_additive : (supportRepresentation R f).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (supportRepresentation R f)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Scalar multiplication on the genuine small supported coherent category. -/
abbrev supportScalar : 𝟭 (SmallSupport R f) ⟶ 𝟭 (SmallSupport R f) :=
  ScalarRepresentation.scalar (supportRepresentation R f) f

/-- The killed objects inside the genuine small supported coherent category. -/
abbrev supportKilled : ObjectProperty (SmallSupport R f) := killed (supportScalar R f)

theorem supportKilled_iff (M : SmallSupport R f) :
    supportKilled R f M ↔ ∀ m : (supportRepresentation R f).obj M, f • m = 0 :=
  ScalarRepresentation.killed_iff (supportRepresentation R f) f M

/-- Nilpotence follows from genuine support and finite generation. -/
theorem support_power_nilpotent (M : SmallSupport R f) :
    ∃ n : ℕ, power (supportScalar R f) M n = 0 := by
  have h := (coherentPrincipalSmallSupport_iff R f M.obj).mp M.property
  obtain ⟨n, hn⟩ := (finiteTypeSheavesSupportedAway_iff_uniform R f _).mp h
  exact ⟨n, ScalarRepresentation.power_eq_zero (supportRepresentation R f) f M n hn⟩

/-- The actual finite image filtration on every supported coherent object. -/
theorem supportFiltrationHypothesis : Devissage.FiltrationHypothesis (supportKilled R f) :=
  PrincipalSupportDevissage.filtrationHypothesis (supportScalar R f) (support_power_nilpotent R f)

/-- Genuine dévissage on the actual compatible support category, in the
public upper universe. Its forward map is the canonical killed inclusion. -/
def supportDevissageKEquiv (n : ℕ) :
    (CategoryTheory.ObjectProperty.subcategoryExactStructure (supportKilled R f)).K n ≃*
      CoherentPrincipalSupportedG R f n :=
  Devissage.KEquiv (supportKilled R f) (supportFiltrationHypothesis R f) n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem supportDevissageKEquiv_coe (n : ℕ) :
    ↑(supportDevissageKEquiv R f n) = Devissage.KMap (supportKilled R f) n := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
