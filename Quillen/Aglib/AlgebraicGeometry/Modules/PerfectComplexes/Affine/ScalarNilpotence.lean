/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.DerivedHom.Nilpotence
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.Affine.PrincipalRestrictionQuasiIso
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.DerivedModuleReplacement
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.PerfectOpenApproximation
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local


public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representatives
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
/-!
# Original scalar nilpotence on compact affine opens

Let P be an actual bounded finite-projective module complex over an arbitrary
commutative ring R, W a compact open in Spec R, and r an element of R. If the
original restricted associated complex is zero in the derived category on
W ∩ D(r), some actual scalar chain map r^n • id_P becomes zero in the original
sheaf derived category on W.

On a contained principal D(q), genuine module homotopy denominators at D(qr)
kill (qr)^n • id_P; the q-power is genuinely invertible on D(q), so it can be
cancelled. A genuine finite principal cover and the proved finite-cover
Mayer–Vietoris nilpotence theorem then supply a global exponent. No supplied
annihilation premise, noetherianity, domain hypothesis, or nonempty-open
assumption occurs. This is the scalar-identity support-forcing input to the
perfect-extension route of Stacks Project, Section 36.13; the broader
arbitrary-map scalar-localization statement is separate.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] HasDerivedCategory.standard
open Quillen.ModuleComplex.PrincipalLocalization

/-- Actual local scalar nilpotence on D(q), obtained by clearing at D(qr)
and cancelling the genuinely invertible q-power on D(q). -/
lemma exists_scalar_power_zero_on_principal_of_localized_isZero
    (R : CommRingCat.{u}) (q r : R) {P : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hz : IsZero (DerivedCategory.Q.obj ((localize (q * r) (.up ℤ)).obj P))) :
    ∃ n : ℕ, (DerivedCategory.Q (C := (Scheme.Opens.toScheme (X := Spec R)
      (PrimeSpectrum.basicOpen q)).Modules)).map
      ((restrict (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen q))).map
        ((associatedComplex R).map (r ^ n • 𝟙 P))) = 0 := by
  have : CochainComplex.IsKProjective ((localize (q*r) (.up ℤ)).obj P) :=
    isKProjective_of_moduleStrictPerfect _ (moduleStrictPerfect_localize R (q*r) hP)
  let H := _root_.CochainComplex.homotopyOfDerivedEqOfIsKProjective
    ((localize (q*r) (.up ℤ)).map (𝟙 P)) ((localize (q*r) (.up ℤ)).map (0 : P ⟶ P))
    (hz.eq_of_src _ _)
  obtain ⟨⟨s, hs⟩, hfp⟩ := moduleStrictPerfect_denominator_inputs R hP
  obtain ⟨n, ⟨Hn⟩⟩ := exists_nullhomotopy_power (q*r) s hs hfp (𝟙 P)
    (by simpa only [Functor.map_zero] using H)
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen q
  let F := associatedComplex R ⋙ restrict U.ι
  have hnull : (DerivedCategory.Q (C := U.toScheme.Modules)).map (F.map ((q*r)^n • 𝟙 P)) = 0 := by
    rw [← (DerivedCategory.Q (C := U.toScheme.Modules)).map_zero]
    apply DerivedCategory.Q_map_eq_of_homotopy _
    simpa only [F, restrict, Functor.comp_map, Functor.comp_obj, Functor.map_zero] using
      ((Scheme.Modules.restrictFunctor U.ι).mapHomotopy ((tilde.functor R).mapHomotopy Hn))
  have hqi : QuasiIso (F.map (q^n • 𝟙 P)) := by
    apply quasiIso_restrict_associated_of_principalUnion R U {q}
    · simp only [Quillen.SheafCohomology.principalUnion, Finset.mem_singleton, iSup_iSup_eq_left, U]
    · intro t ht
      have : t = q := by simpa using ht
      subst t
      have := localize_power_id_isIso q P n
      infer_instance
  have he : (q*r)^n • 𝟙 P = (q^n • 𝟙 P) ≫ (r^n • 𝟙 P) := by
    simp only [mul_pow, Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, mul_comm]
  rw [he, F.map_comp, Functor.map_comp] at hnull
  refine ⟨n, ?_⟩
  change (DerivedCategory.Q (C := U.toScheme.Modules)).map (F.map (r^n • 𝟙 P)) = 0
  apply (cancel_epi ((DerivedCategory.Q (C := U.toScheme.Modules)).map (F.map (q^n • 𝟙 P)))).mp
  simpa only [comp_zero] using hnull

/-- Genuine zero detection of the localized module complex from its original
associated restriction to a surrounding open. -/
lemma isZero_localize_of_isZero_restrict_associated (R : CommRingCat.{u})
    (W : (Spec R).Opens) (P : ModuleComplex R)
    (hz : IsZero ((DerivedCategory.Q (C := W.toScheme.Modules)).obj
      ((restrict W.ι).obj ((associatedComplex R).obj P))))
    (q : R) (hq : PrimeSpectrum.basicOpen q ≤ W) :
    IsZero (DerivedCategory.Q.obj ((localize q (.up ℤ)).obj P)) := by
  have hw : QuasiIso ((restrict W.ι).map ((associatedComplex R).map (0 : P ⟶ P))) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso W.toScheme.Modules _).mp
    exact hz.isIso hz _
  have hq' := quasiIso_localize_of_restrict_associated R W (0 : P ⟶ P) q hq
  have hi : IsIso (DerivedCategory.Q.map ((localize q (.up ℤ)).map (0 : P ⟶ P))) := inferInstance
  simp only [Functor.map_zero] at hi
  exact (isIsoZero_iff_source_target_isZero _ _).mp hi |>.1

/-- The affine principal leaf uses acyclicity only on the given intersection. -/
lemma exists_scalar_power_zero_on_contained_principal (R : CommRingCat.{u})
    (W : (Spec R).Opens) (q r : R) (hq : PrimeSpectrum.basicOpen q ≤ W)
    {P : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hz : IsZero ((DerivedCategory.Q (C := (W ⊓ PrimeSpectrum.basicOpen r).toScheme.Modules)).obj
      ((restrict (W ⊓ PrimeSpectrum.basicOpen r).ι).obj ((associatedComplex R).obj P)))) :
    ∃ n : ℕ, (DerivedCategory.Q (C := (Scheme.Opens.toScheme (X := Spec R)
      (PrimeSpectrum.basicOpen q)).Modules)).map
      ((restrict (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen q))).map
        ((associatedComplex R).map (r ^ n • 𝟙 P))) = 0 := by
  apply exists_scalar_power_zero_on_principal_of_localized_isZero R q r hP
  apply isZero_localize_of_isZero_restrict_associated R (W ⊓ PrimeSpectrum.basicOpen r) P hz (q*r)
  rw [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf hq le_rfl
end Quillen.PerfectComplexes.Affine

namespace Quillen.PerfectComplexes.Affine
attribute [local instance] HasDerivedCategory.standard
open Quillen.ModuleComplex.PrincipalLocalization

lemma moduleComplex_scalar_id_pow (R : CommRingCat.{u}) (P : ModuleComplex R) (r : R) (n : ℕ) :
    (r • (1 : End P))^n = r^n • (1 : End P) := by
  induction n with
  | zero => simp only [pow_zero, one_smul]
  | succ n ih =>
    rw [pow_succ, ih, End.mul_def, Linear.smul_comp, Linear.comp_smul]
    change r • r^n • (𝟙 P ≫ 𝟙 P) = r^(n+1) • 𝟙 P
    rw [Category.id_comp, smul_smul, pow_succ, mul_comm r]

/-- A global finite-projective source which is acyclic on W∩D(r) has an
actual scalar power of its identity zero in the ORIGINAL derived category
on W. The genuine finite MV induction supplies the global exponent. -/
theorem exists_scalar_power_zero_of_isZero_on_intersection
    (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (r : R) {P : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hz : IsZero ((DerivedCategory.Q (C := (W ⊓ PrimeSpectrum.basicOpen r).toScheme.Modules)).obj
      ((restrict (W ⊓ PrimeSpectrum.basicOpen r).ι).obj ((associatedComplex R).obj P)))) :
    ∃ n : ℕ, (DerivedCategory.Q (C := W.toScheme.Modules)).map
      ((restrict W.ι).map ((associatedComplex R).map (r^n • 𝟙 P))) = 0 := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_principal_cover R W hW
  let f : End ((associatedComplex R).obj P) := (associatedComplex R).map (r • 𝟙 P)
  have hf (n : ℕ) : f^n = (associatedComplex R).map (r^n • 𝟙 P) := by
    change ((associatedComplex R).mapEnd P (r • (1 : End P)))^n =
      (associatedComplex R).mapEnd P (r^n • (1 : End P))
    rw [← map_pow, moduleComplex_scalar_id_pow]
  let t : Finset (Spec R).Opens := s.image (fun q => PrimeSpectrum.basicOpen q)
  have hlocal (U : (Spec R).Opens) (hU : U ∈ t) : DerivedNilpotentOn f U := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hU
    have hqW : PrimeSpectrum.basicOpen q ≤ W := by
      rw [← hs]
      exact Quillen.SheafCohomology.basicOpen_le_principalUnion R hq
    obtain ⟨n, hn⟩ := exists_scalar_power_zero_on_contained_principal R W q r hqW hP hz
    exact ⟨n, by rw [hf]; exact hn⟩
  have ht : t.sup id = W := by
    rw [← hs]
    dsimp only [t]
    rw [Finset.sup_image]
    simp only [Function.comp_def, id_eq, Finset.sup_eq_iSup,
      Quillen.SheafCohomology.principalUnion]
  obtain ⟨n, hn⟩ := derivedNilpotentOn_finite_union f t hlocal
  rw [ht, hf] at hn
  exact ⟨n, hn⟩
end Quillen.PerfectComplexes.Affine
