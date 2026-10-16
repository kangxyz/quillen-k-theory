/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.FGModuleCat.IdealClosedSupport
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Stalk
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.IdealPushforward
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Support
public import Mathlib.RingTheory.Finiteness.Ideal

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ClosedImmersion
/-!
# The support bridge for an arbitrary affine closed subscheme

Vanishing on the open complement of V(I) is equivalent to the actual finite
global-section module being annihilated by a power of I. The intermediate
radical-annihilator criterion follows from ordinary stalk support, not from
an assumed localization or dévissage equivalence.
-/
@[expose] public section

open ModuleCat.FiniteLocalization.IdealClosedSupport


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal

variable (R : CommRingCat.{u}) (I : Ideal R)

/-- The actual open complement of the closed subset V(I) in Spec R. -/
def openComplement : (Spec R).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus (I : Set R)).isOpen_compl⟩

/-- Inclusion of the actual open complement of the affine closed subscheme. -/
def openMap : (openComplement R I).toScheme ⟶ Spec R := (openComplement R I).ι

instance openMap_isOpenImmersion : IsOpenImmersion (openMap R I) := by
  unfold openMap
  infer_instance

@[simp] theorem openMap_range :
    Set.range (openMap R I) = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ := by
  change Set.range (openComplement R I).ι = _
  rw [Scheme.Opens.range_ι]
  rfl

theorem openMap_range_compl :
    (Set.range (openMap R I))ᶜ = PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [openMap_range, compl_compl]

variable [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- Actual geometric support in V(I) is the radical-annihilator condition
on the actual finite global-section module. -/
theorem finiteTypeSheavesSupportedAway_iff_le_radical_annihilator (M : FiniteTypeSheaves (Spec R)) :
    finiteTypeSheavesSupportedAway (openMap R I) M ↔
      I ≤ (Module.annihilator R ((finiteTypeSheavesSpecModuleEquivalence R).functor.obj M)).radical
        := by
  have hM := (affineLocallyFiniteType_spec_iff R M.obj).mp M.property
  have : M.obj.IsQuasicoherent := hM.1
  have : Module.Finite R (moduleSpecΓFunctor.obj M.obj) := hM.2
  rw [finiteTypeSheavesSupportedAway_iff_support_subset, openMap_range_compl,
    AlgebraicGeometry.Scheme.Modules.support_eq_support_globalSections, Module.support_eq_zeroLocus,
    PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
  rfl

/-- Noetherian finite generation makes the ideal-power exponent uniform. -/
theorem finiteTypeSheavesSupportedAway_iff_pow_le_annihilator (M : FiniteTypeSheaves (Spec R)) :
    finiteTypeSheavesSupportedAway (openMap R I) M ↔ ∃ n : ℕ,
      I ^ n ≤ Module.annihilator R ((finiteTypeSheavesSpecModuleEquivalence R).functor.obj M) := by
  rw [finiteTypeSheavesSupportedAway_iff_le_radical_annihilator]
  constructor
  · intro h
    exact Ideal.exists_pow_le_of_le_radical_of_fg h I.fg_of_isNoetherianRing
  · rintro ⟨n, hn⟩ r hr
    exact ⟨n, hn (Ideal.pow_mem_pow hr n)⟩

omit [IsNoetherianRing R] in
/-- Each element of I acts nilpotently on every section, with one exponent
for the whole finite module. -/
theorem finiteTypeSheavesSupportedAway_iff_elementwise_uniform (M : FiniteTypeSheaves (Spec R)) :
    finiteTypeSheavesSupportedAway (openMap R I) M ↔ ∀ r ∈ I, ∃ n : ℕ,
      ∀ m : (finiteTypeSheavesSpecModuleEquivalence R).functor.obj M, r ^ n • m = 0 := by
  rw [finiteTypeSheavesSupportedAway_iff_le_radical_annihilator]
  simp only [SetLike.le_def, Ideal.mem_radical_iff, Module.mem_annihilator]

omit [IsNoetherianRing R] in
/-- Elementwise nilpotence extracted from genuine geometric support. -/
theorem supported_power_annihilates (M : FiniteTypeSheaves (Spec R))
    (hM : finiteTypeSheavesSupportedAway (openMap R I) M) (r : R) (hr : r ∈ I) :
    ∃ n : ℕ, ∀ m : (finiteTypeSheavesSpecModuleEquivalence R).functor.obj M, r ^ n • m = 0 :=
  (finiteTypeSheavesSupportedAway_iff_elementwise_uniform R I M).mp hM r hr

/-- One ideal-power annihilates all actual finite global sections. -/
theorem finiteTypeSheavesSupportedAway_iff_uniform (M : FiniteTypeSheaves (Spec R)) :
    finiteTypeSheavesSupportedAway (openMap R I) M ↔ ∃ n : ℕ, ∀ r ∈ I ^ n,
      ∀ m : (finiteTypeSheavesSpecModuleEquivalence R).functor.obj M, r • m = 0 := by
  rw [finiteTypeSheavesSupportedAway_iff_pow_le_annihilator]
  simp only [SetLike.le_def, Module.mem_annihilator]

omit [IsNoetherianRing R] in
/-- Annihilation by I implies genuine geometric support in V(I). -/
theorem finiteTypeSheavesKilledBy_le_supportedAway :
    finiteTypeSheavesKilledBy R I ≤ finiteTypeSheavesSupportedAway (openMap R I) := by
  intro M hM
  apply (finiteTypeSheavesSupportedAway_iff_le_radical_annihilator R I M).mpr
  exact ((killedBy_iff_le_annihilator I _).mp hM).trans Ideal.le_radical

omit [IsNoetherianRing R] in
/-- Actual quotient closed pushforward is supported on its closed subset. -/
theorem coherentPushforward_supported (M : FiniteTypeSheaves (Spec
  (Pushforward.ClosedImmersion.Ideal.closedRing R I))) :
    finiteTypeSheavesSupportedAway (openMap R I)
      ((finiteTypePushforward (Pushforward.ClosedImmersion.Ideal.closedMap R I)).obj M) := by
  apply (finiteTypeSheavesSupportedAway_iff_support_subset (openMap R I) _).mpr
  rw [openMap_range_compl]
  change Scheme.Modules.support
      ((Scheme.Modules.pushforward (Pushforward.ClosedImmersion.Ideal.closedMap R I)).obj M.obj) ⊆
    PrimeSpectrum.zeroLocus (I : Set R)
  intro x hx
  by_contra hxi
  have hnot : x ∉ Set.range (Pushforward.ClosedImmersion.Ideal.closedMap R I) := by
    rintro ⟨y, rfl⟩
    apply hxi
    intro r hr
    change Ideal.Quotient.mk I r ∈ y.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact y.asIdeal.zero_mem
  have hz := Scheme.Modules.isZero_closedImmersion_moduleStalk_of_not_mem
    (Pushforward.ClosedImmersion.Ideal.closedMap R I) x hnot M.obj
  have hzAb := (forget₂ (ModuleCat ((Spec R).presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero hz
  exact hx (hzAb.of_iso ((Scheme.Modules.moduleStalkForgetIso (Spec R) x).app
    ((Scheme.Modules.pushforward (Pushforward.ClosedImmersion.Ideal.closedMap R I)).obj
      M.obj)).symm)

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
