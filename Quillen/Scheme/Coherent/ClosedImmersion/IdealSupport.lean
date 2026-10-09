import Quillen.Scheme.Coherent.ClosedImmersion.IdealPushforward
import Quillen.Scheme.Coherent.Restriction
import Quillen.Scheme.Sheaf.AffineSupport
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# The support bridge for an arbitrary affine closed subscheme

Vanishing on the open complement of V(I) is equivalent to the actual finite
global-section module being annihilated by a power of I. The intermediate
radical-annihilator criterion follows from ordinary stalk support, not from
an assumed localization or dévissage equivalence.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme.ClosedImmersion.Ideal
open FiniteModuleLocalization.IdealClosedSupport

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

@[simp] theorem openMap_range_compl :
    (Set.range (openMap R I))ᶜ = PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [openMap_range, compl_compl]

variable [IsNoetherianRing R]

/-- Actual geometric support in V(I) is the radical-annihilator condition
on the actual finite global-section module. -/
theorem coherentSupportedAway_iff_le_radical_annihilator (M : Coherent (Spec R)) :
    coherentSupportedAway (openMap R I) M ↔
      I ≤ (Module.annihilator R ((coherentSpecModuleEquivalence R).functor.obj M)).radical := by
  have hM := (coherent_spec_iff R M.obj).mp M.property
  have : M.obj.IsQuasicoherent := hM.1
  have : Module.Finite R (moduleSpecΓFunctor.obj M.obj) := hM.2
  rw [coherentSupportedAway_iff_support_subset, openMap_range_compl,
    SchemeSheaf.support_eq_support_globalSections, Module.support_eq_zeroLocus,
    PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
  rfl

/-- Noetherian finite generation makes the ideal-power exponent uniform. -/
theorem coherentSupportedAway_iff_pow_le_annihilator (M : Coherent (Spec R)) :
    coherentSupportedAway (openMap R I) M ↔ ∃ n : ℕ,
      I ^ n ≤ Module.annihilator R ((coherentSpecModuleEquivalence R).functor.obj M) := by
  rw [coherentSupportedAway_iff_le_radical_annihilator]
  constructor
  · intro h
    exact Ideal.exists_pow_le_of_le_radical_of_fg h I.fg_of_isNoetherianRing
  · rintro ⟨n, hn⟩ r hr
    exact ⟨n, hn (Ideal.pow_mem_pow hr n)⟩

/-- Each element of I acts nilpotently on every section, with one exponent
for the whole finite module. -/
theorem coherentSupportedAway_iff_elementwise_uniform (M : Coherent (Spec R)) :
    coherentSupportedAway (openMap R I) M ↔ ∀ r ∈ I, ∃ n : ℕ,
      ∀ m : (coherentSpecModuleEquivalence R).functor.obj M, r ^ n • m = 0 := by
  rw [coherentSupportedAway_iff_le_radical_annihilator]
  simp only [SetLike.le_def, Ideal.mem_radical_iff, Module.mem_annihilator]

/-- Elementwise nilpotence extracted from genuine geometric support. -/
theorem supported_power_annihilates (M : Coherent (Spec R))
    (hM : coherentSupportedAway (openMap R I) M) (r : R) (hr : r ∈ I) :
    ∃ n : ℕ, ∀ m : (coherentSpecModuleEquivalence R).functor.obj M, r ^ n • m = 0 :=
  (coherentSupportedAway_iff_elementwise_uniform R I M).mp hM r hr

/-- One ideal-power annihilates all actual finite global sections. -/
theorem coherentSupportedAway_iff_uniform (M : Coherent (Spec R)) :
    coherentSupportedAway (openMap R I) M ↔ ∃ n : ℕ, ∀ r ∈ I ^ n,
      ∀ m : (coherentSpecModuleEquivalence R).functor.obj M, r • m = 0 := by
  rw [coherentSupportedAway_iff_pow_le_annihilator]
  simp only [SetLike.le_def, Module.mem_annihilator]

/-- Annihilation by I implies genuine geometric support in V(I). -/
theorem coherentKilledBy_le_supportedAway :
    coherentKilledBy R I ≤ coherentSupportedAway (openMap R I) := by
  intro M hM
  apply (coherentSupportedAway_iff_le_radical_annihilator R I M).mpr
  exact ((killedBy_iff_le_annihilator I _).mp hM).trans Ideal.le_radical

/-- Actual quotient closed pushforward is supported on its closed subset. -/
theorem coherentPushforward_supported (M : Coherent (Spec (closedRing R I))) :
    coherentSupportedAway (openMap R I) ((coherentPushforward R I).obj M) :=
  coherentKilledBy_le_supportedAway R I _ (coherentPushforward_killed R I M)

end Quillen.CoherentScheme.ClosedImmersion.Ideal
