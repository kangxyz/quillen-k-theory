/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Algebra.Homology.FiniteProjectiveResolution
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Lifting finite free syzygies through a regular parameter

These are genuine homological induction steps. The scalar is required to be
regular on the ring and on the resolved module. A projective-dimension bound
on the quotient module over the smaller quotient ring produces an actual
finite free resolution over the original local ring. No K-theory comparison
or general regular-local theorem is assumed here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped Pointwise
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.RegularLocal
variable {R : Type u} [CommRing R]

/-- The scalar-quotient map as a map over the quotient ring itself. -/
def quotientLinearMap (x : R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    QuotSMulTop x M →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x N :=
  (QuotSMulTop.map x f.hom).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- The actual quotient-by-a-scalar short complex, with quotient-ring scalars. -/
def quotientShortComplex (x : R) (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} (R ⧸ Ideal.span {x})) :=
  ShortComplex.moduleCatMk (quotientLinearMap x S.f) (quotientLinearMap x S.g) (by
    apply LinearMap.restrictScalars_injective R
    change (QuotSMulTop.map x S.g.hom).comp (QuotSMulTop.map x S.f.hom) = 0
    rw [← QuotSMulTop.map_comp]
    have h : S.g.hom.comp S.f.hom = 0 := congrArg ModuleCat.Hom.hom S.zero
    rw [h, map_zero])

/-- Reduction modulo a scalar preserves a short exact sequence when the
scalar is regular on its quotient term. -/
theorem quotientShortComplex_shortExact (x : R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (hx : IsSMulRegular S.X₃ x) :
    (quotientShortComplex x S).ShortExact := by
  have he : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hi : Function.Injective (QuotSMulTop.map x S.f.hom) := by
    have he0 : Function.Exact (0 : S.X₁ →ₗ[R] S.X₁) S.f.hom :=
      (LinearMap.exact_zero_iff_injective S.X₁ S.f.hom).mpr hS.moduleCat_injective_f
    have hq := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last he0 he hx
    simpa using hq
  exact {
    exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      (QuotSMulTop.map_exact x he hS.moduleCat_surjective_g)
    mono_f := (ModuleCat.mono_iff_injective _).mpr hi
    epi_g := (ModuleCat.epi_iff_surjective _).mpr
      (QuotSMulTop.map_surjective x hS.moduleCat_surjective_g) }

/-- A ring-regular scalar acts injectively on every free module. -/
theorem isSMulRegular_free (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{u} R) [Module.Free R M] : IsSMulRegular M x := by
  let b := Module.Free.chooseBasis R M
  exact (b.repr.isSMulRegular_congr x).mpr hx.finsupp

variable (R) [IsNoetherianRing R] [IsLocalRing R]

/-- A finite projective-dimension bound after reduction by a regular
parameter lifts to an actual finite free resolution before reduction.
This is the homological induction step over the smaller quotient ring. -/
theorem finiteFreeResolution_of_quotientProjectiveDimension
    (x : R) (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x)
    (n : ℕ) (M : CoherentScheme.FiniteModule.{u, u} R) (hxM : IsSMulRegular M.obj x)
    [HasProjectiveDimensionLE (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M.obj)) n] :
    ∃ T : (CoherentScheme.finiteModuleExactStructure R).FiniteResolution
      (fun N => Module.Free R N.obj) M, T.length ≤ n := by
  have hne : Ideal.span {x} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top ((Ideal.span_singleton_le_iff_mem
      (maximalIdeal R)).mpr hx)
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  have hxJ : x ∈ (⊥ : Ideal R).jacobson := (maximalIdeal_le_jacobson _) hx
  induction n generalizing M with
  | zero =>
    let Q := ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M.obj)
    have hP : Projective Q :=
      (projective_iff_hasProjectiveDimensionLE_zero Q).mpr inferInstance
    have : Module.Projective (R ⧸ Ideal.span {x}) (QuotSMulTop x M.obj) :=
      (IsProjective.iff_projective _).mpr hP
    have : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M.obj) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) _
    have hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M.obj) :=
      Module.free_of_flat_of_isLocalRing
    have : Module.FinitePresentation R M.obj := Module.finitePresentation_of_finite R M.obj
    exact ⟨.of_mem ((Module.free_quotSMulTop_iff_free R M.obj hxJ hxM).mp hfree), le_rfl⟩
  | succ n ih =>
    obtain ⟨K, P, i, p, w, hfree, hS⟩ := CoherentScheme.exists_finiteFree_shortExact R M
    have : Module.Free R P.obj := hfree
    let S := (ShortComplex.mk i p w).map (CoherentScheme.finiteModule R).ι
    have hS' : S.ShortExact := (CoherentScheme.finiteModule_shortExact_iff R _).mp hS
    have hxK : IsSMulRegular K.obj x :=
      (isSMulRegular_free x hxR P.obj).of_injective i.hom.hom hS'.moduleCat_injective_f
    have hQ := quotientShortComplex_shortExact x S hS' hxM
    have hQP : Projective (quotientShortComplex x S).X₂ := by
      change Projective (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x P.obj))
      infer_instance
    have hQM : HasProjectiveDimensionLT (quotientShortComplex x S).X₃ (n + 2) := by
      change HasProjectiveDimensionLE
        (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M.obj)) (n + 1)
      infer_instance
    have : HasProjectiveDimensionLE
        (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x K.obj)) n :=
      (hQ.hasProjectiveDimensionLT_X₃_iff n hQP).mp hQM
    obtain ⟨T, hT⟩ := ih K hxK
    exact ⟨.step (ShortComplex.mk i p w) hS hfree T, Nat.succ_le_succ hT⟩

omit [IsLocalRing R] in
/-- A tower of actual finite free conflations has the expected Ext-defined
projective-dimension bound. This is proved recursively from exact sequences. -/
theorem finiteFreeResolution_hasProjectiveDimensionLE
    {M : CoherentScheme.FiniteModule.{u, u} R}
    (T : (CoherentScheme.finiteModuleExactStructure R).FiniteResolution
      (fun N => Module.Free R N.obj) M) : HasProjectiveDimensionLE M.obj T.length := by
  induction T with
  | @of_mem N hN =>
    have : Module.Free R N.obj := hN
    change HasProjectiveDimensionLE N.obj 0
    infer_instance
  | step S hS hP T ih =>
    have : Module.Free R S.X₂.obj := hP
    have hS' := (CoherentScheme.finiteModule_shortExact_iff R S).mp hS
    have hP' : Projective (S.map (CoherentScheme.finiteModule R).ι).X₂ := by
      change Projective S.X₂.obj
      infer_instance
    exact (hS'.hasProjectiveDimensionLT_X₃_iff T.length hP').mpr ih

omit [IsLocalRing R] in
/-- A tower whose length is bounded by `n` supplies the corresponding
independent projective-dimension bound. -/
theorem hasProjectiveDimensionLE_of_finiteFreeResolution
    {M : CoherentScheme.FiniteModule.{u, u} R}
    (T : (CoherentScheme.finiteModuleExactStructure R).FiniteResolution
      (fun N => Module.Free R N.obj) M) (n : ℕ) (hT : T.length ≤ n) :
    HasProjectiveDimensionLE M.obj n := by
  have := finiteFreeResolution_hasProjectiveDimensionLE R T
  exact hasProjectiveDimensionLT_of_ge M.obj (T.length + 1) (n + 1) (Nat.succ_le_succ hT)

/-- Taking a first finite-free syzygy makes an arbitrary finite module
regular with respect to the parameter. A bound for all finite modules over
the smaller quotient ring therefore gives an actual finite-free resolution
of every finite module over `R`, with one extra step. -/
theorem finiteFreeResolution_of_quotientRingBound
    (x : R) (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) (n : ℕ)
    (h : ∀ N : ModuleCat.{u} (R ⧸ Ideal.span {x}), Module.Finite (R ⧸ Ideal.span {x}) N →
      HasProjectiveDimensionLE N n)
    (M : CoherentScheme.FiniteModule.{u, u} R) :
    ∃ T : (CoherentScheme.finiteModuleExactStructure R).FiniteResolution
      (fun N => Module.Free R N.obj) M, T.length ≤ n + 1 := by
  obtain ⟨K, P, i, p, w, hfree, hS⟩ := CoherentScheme.exists_finiteFree_shortExact R M
  have : Module.Free R P.obj := hfree
  have hS' := (CoherentScheme.finiteModule_shortExact_iff R _).mp hS
  have hxK : IsSMulRegular K.obj x :=
    (isSMulRegular_free x hxR P.obj).of_injective i.hom.hom hS'.moduleCat_injective_f
  have hfin : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x K.obj) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) _
  have := h (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x K.obj)) hfin
  obtain ⟨T, hT⟩ := finiteFreeResolution_of_quotientProjectiveDimension R x hx hxR n K hxK
  exact ⟨.step (ShortComplex.mk i p w) hS hfree T, Nat.succ_le_succ hT⟩

/-- The same dimension-induction step stated as an Ext-vanishing bound,
proved from the actual tower constructed immediately above. -/
theorem hasProjectiveDimensionLE_of_quotientRingBound
    (x : R) (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) (n : ℕ)
    (h : ∀ N : ModuleCat.{u} (R ⧸ Ideal.span {x}), Module.Finite (R ⧸ Ideal.span {x}) N →
      HasProjectiveDimensionLE N n)
    (M : ModuleCat.{u} R) [Module.Finite R M] : HasProjectiveDimensionLE M (n + 1) := by
  let N : CoherentScheme.FiniteModule.{u, u} R := ⟨M, (show Module.Finite R M from inferInstance)⟩
  obtain ⟨T, hT⟩ := finiteFreeResolution_of_quotientRingBound R x hx hxR n h N
  exact hasProjectiveDimensionLE_of_finiteFreeResolution R T (n + 1) hT

end Quillen.RegularLocal
