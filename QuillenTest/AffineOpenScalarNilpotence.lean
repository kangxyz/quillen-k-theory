/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.ScalarNilpotence
public import Mathlib.Data.ZMod.Basic


/-! # Original-map consumers of finite-cover and affine scalar nilpotence -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace QuillenTest.AffineOpenScalarNilpotence

open Quillen
open PerfectComplexes PerfectComplexes.Affine
attribute [local instance] HasDerivedCategory.standard

/-- The literal scalar power kills every original derived outgoing map,
including maps to unrestricted all-sheaf targets. -/
theorem original_power_kills_arbitrary_derived_postcomposition
    (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (r : R) {P : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hz : IsZero ((toDerived (W ⊓ PrimeSpectrum.basicOpen r).toScheme).obj
      ((restrict (W ⊓ PrimeSpectrum.basicOpen r).ι).obj ((associatedComplex R).obj P))))
    (L : Complex W.toScheme)
    (α : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ⟶
      (toDerived W.toScheme).obj L) :
    ∃ n : ℕ, (toDerived W.toScheme).map
      ((restrict W.ι).map ((associatedComplex R).map (r^n • 𝟙 P))) ≫ α = 0 := by
  obtain ⟨n, hn⟩ := exists_scalar_power_zero_of_isZero_on_intersection R W hW r hP hz
  exact ⟨n, by rw [hn, zero_comp]⟩

/-- An invertible scalar test on the actual original object: r=1 forces the
identity itself to vanish, rather than merely producing an abstract exponent. -/
theorem one_scalar_original_identity
    (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hz : IsZero ((toDerived (W ⊓ PrimeSpectrum.basicOpen (1 : R)).toScheme).obj
      ((restrict (W ⊓ PrimeSpectrum.basicOpen (1 : R)).ι).obj ((associatedComplex R).obj P)))) :
    𝟙 ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P))) = 0 := by
  obtain ⟨n, hn⟩ := exists_scalar_power_zero_of_isZero_on_intersection R W hW 1 hP hz
  rw [one_pow, one_smul, (associatedComplex R).map_id, (restrict W.ι).map_id,
    (toDerived W.toScheme).map_id] at hn
  exact hn

/-- The empty-open edge uses an arbitrary ring and original finite-perfect
complex; no nonempty cover or nonzero localization is required. -/
theorem empty_open_original_power (R : CommRingCat.{u}) (r : R)
    {P : ModuleComplex R} (hP : moduleStrictPerfect R P) :
    ∃ n : ℕ, (toDerived (⊥ : (Spec R).Opens).toScheme).map
      ((restrict (⊥ : (Spec R).Opens).ι).map ((associatedComplex R).map (r^n • 𝟙 P))) = 0 := by
  apply exists_scalar_power_zero_of_isZero_on_intersection R ⊥ isCompact_empty r hP
  have h0 : IsZero ((restrict (⊥ : (Spec R).Opens).ι).obj ((associatedComplex R).obj P)) := by
    rw [IsZero.iff_id_eq_zero]
    ext i : 1
    have hz : IsZero (((restrict (⊥ : (Spec R).Opens).ι).obj ((associatedComplex R).obj P)).X i) :=
      by
      rw [SchemeSheaf.isZero_iff_stalks]
      intro x
      exact False.elim x.property
    exact hz.eq_of_src _ _
  rw [show (⊥ : (Spec R).Opens) ⊓ PrimeSpectrum.basicOpen r = ⊥ from bot_inf_eq _]
  exact (toDerived (⊥ : (Spec R).Opens).toScheme).map_isZero h0

/-- Actual local zero maps compose to zero on the union, with an arbitrary
final derived target and no QC/perfect assumptions on the complexes. -/
theorem original_mayerVietoris_composite
    {X : Scheme.{u}} {E L M : Complex X} (f : E ⟶ L) (g : L ⟶ M) (U V : X.Opens)
    (hU : (toDerived U.toScheme).map ((restrict U.ι).map f) = 0)
    (hV : (toDerived V.toScheme).map ((restrict V.ι).map f) = 0)
    (hg : (toDerived U.toScheme).map ((restrict U.ι).map g) = 0)
    (T : Derived (U ⊔ V).toScheme)
    (β : (toDerived (U ⊔ V).toScheme).obj ((restrict (U ⊔ V).ι).obj M) ⟶ T) :
    (toDerived (U ⊔ V).toScheme).map ((restrict (U ⊔ V).ι).map f) ≫
      (toDerived (U ⊔ V).toScheme).map ((restrict (U ⊔ V).ι).map g) ≫ β = 0 := by
  have h := toDerived_restrict_comp_eq_zero_on_openUnion f g U V hU hV hg
  rw [Functor.map_comp, Functor.map_comp] at h
  rw [← Category.assoc, h, zero_comp]

/-- A finite cover detects genuine nilpotence even for arbitrary all-sheaf
complexes, with the original chain power retained in the conclusion. -/
theorem finite_family_original_chain_power
    {X : Scheme.{u}} {E : Complex X} (f : End E) (s : Finset X.Opens)
    (hs : ∀ U ∈ s, ∃ n : ℕ, (toDerived U.toScheme).map ((restrict U.ι).map (f^n)) = 0) :
    ∃ n : ℕ, ∀ {T : Derived (s.sup id).toScheme}
      (α : (toDerived (s.sup id).toScheme).obj ((restrict (s.sup id).ι).obj E) ⟶ T),
      (toDerived (s.sup id).toScheme).map ((restrict (s.sup id).ι).map (f^n)) ≫ α = 0 := by
  obtain ⟨n, hn⟩ := derivedNilpotentOn_finite_union f s hs
  exact ⟨n, fun α => by rw [hn, zero_comp]⟩
/-- The actual disjoint principal opens D(3) and D(2) in Spec(Z/6) test
zero divisors and the empty localized intersection without any acyclicity input. -/
theorem zero_divisor_disjoint_principals
    (P : ModuleComplex (.of (ZMod 6))) (hP : moduleStrictPerfect (.of (ZMod 6)) P) :
    let W : (Spec (.of (ZMod 6))).Opens := PrimeSpectrum.basicOpen (3 : ZMod 6)
    ∃ n : ℕ, (toDerived W.toScheme).map
      ((restrict W.ι).map ((associatedComplex (.of (ZMod 6))).map ((2 : ZMod 6)^n • 𝟙 P))) = 0 := by
  intro W
  apply exists_scalar_power_zero_of_isZero_on_intersection (.of (ZMod 6)) W
    (PrimeSpectrum.isCompact_basicOpen _) 2 hP
  have hW : W ⊓ PrimeSpectrum.basicOpen (2 : ZMod 6) = ⊥ := by
    change PrimeSpectrum.basicOpen (3 : ZMod 6) ⊓ PrimeSpectrum.basicOpen 2 = ⊥
    rw [← PrimeSpectrum.basicOpen_mul, show (3 : ZMod 6)*2 = 0 by decide,
      PrimeSpectrum.basicOpen_zero]
  rw [hW]
  apply (toDerived (⊥ : (Spec (.of (ZMod 6))).Opens).toScheme).map_isZero
  rw [IsZero.iff_id_eq_zero]
  ext i : 1
  have hz : IsZero (((restrict (⊥ : (Spec (.of (ZMod 6))).Opens).ι).obj
      ((associatedComplex (.of (ZMod 6))).obj P)).X i) := by
    rw [SchemeSheaf.isZero_iff_stalks]
    intro x
    exact False.elim x.property
  exact hz.eq_of_src _ _

end QuillenTest.AffineOpenScalarNilpotence
