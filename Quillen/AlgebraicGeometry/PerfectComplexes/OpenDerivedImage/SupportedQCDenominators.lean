/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenUnitConeConstruction
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Models
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedHom.SupportedCocone

/-! # From genuine supported QC denominators to original open roofs

The remaining geometric input is stated explicitly: annihilation of maps from
perfect sources to lower-bounded QC-homology targets which vanish on the open.
The actual injective restriction-unit cone turns that property into the original
HasDerivedRoofs interface. Genuine globally weak fractions give both final
chain arrows. The same property kills any original derived map restricting to
zero, through the literal unit mapping cocone.

These are conditional reduction theorems. No geometric factorization, roof,
K-theory equivalence or localization conclusion is assumed as an axiom.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
/-- The standard derived model used for supported quasicoherent denominators. -/
local instance qcDenominatorDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

namespace OpenDerivedImage
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Geometric annihilating denominators for genuinely supported lower-bounded QC targets. -/
def HasSupportedQCDenominators : Prop :=
  ∀ (A B : Complex X), locallyPerfect X A → ∀ b : ℤ, B.IsGE b →
    (∀ n, (B.homology n).IsQuasicoherent) →
    IsZero ((toDerived U).obj ((restrict j).obj B)) →
    ∀ α : (toDerived X).obj A ⟶ (toDerived X).obj B,
      ∃ (M : Complex X) (q : M ⟶ A), locallyPerfect X M ∧
        QuasiIso ((restrict j).map q) ∧ (toDerived X).map q ≫ α = 0

/-- Original supported factorization through an actual global perfect chain model. -/
def HasSupportedQCFactorizations : Prop :=
  ∀ (A B : Complex X), locallyPerfect X A → ∀ b : ℤ, B.IsGE b →
    (∀ n, (B.homology n).IsQuasicoherent) →
    IsZero ((toDerived U).obj ((restrict j).obj B)) →
    ∀ α : (toDerived X).obj A ⟶ (toDerived X).obj B,
      ∃ (C : Complex X) (i : A ⟶ C) (γ : (toDerived X).obj C ⟶ (toDerived X).obj B),
        locallyPerfect X C ∧ (toDerived X).map i ≫ γ = α ∧
          IsZero ((toDerived U).obj ((restrict j).obj C))

/-- Actual supported perfect factorizations give original weak denominators via the literal cocone.
-/
lemma hasSupportedQCDenominators_of_factorizations
    (h : HasSupportedQCFactorizations j) : HasSupportedQCDenominators j := by
  intro A B hA b hb hqc hz α
  obtain ⟨C, i, γ, hC, heq, hzC⟩ := h A B hA b hb hqc hz α
  refine ⟨CochainComplex.mappingCocone i, CochainComplex.mappingCocone.fst i,
    locallyPerfect_mappingCocone hA hC i, quasiIso_restrict_mappingCocone_fst_of_isZero j i hzC, ?_⟩
  have hi : (toDerived X).map (CochainComplex.mappingCocone.fst i) ≫ (toDerived X).map i = 0 :=
    comp_distTriang_mor_zero₁₂ _ (DerivedCategory.mappingCocone_triangle_distinguished i)
  rw [← heq, ← Category.assoc, hi, zero_comp]

/-- The proved original unit-cone construction converts geometric supported denominators
into actual global-model roofs. The geometric denominator property is explicit. -/
lemma hasDerivedRoofs_of_supportedQCDenominators [CompactSpace X] [QuasiCompact j]
    (h : HasSupportedQCDenominators j) : HasDerivedRoofs j := by
  intro A P hA hP φ
  obtain ⟨b, c, hboundP⟩ := locallyPerfect_homology_bounded hP
  have : P.IsGE b := (CochainComplex.isGE_iff P b).mpr (fun n hn =>
    (HomologicalComplex.exactAt_iff_isZero_homology P n).mpr (hboundP n (Or.inl hn)))
  obtain ⟨I, q, hIb, hi, hq, hCqc, hCb, hzC⟩ :=
    exists_restrictionUnitCone_model j P b (locallyPerfect_quasicoherent_homology hP)
  let := hq
  have hbI : ∀ n, n < b → IsZero (I.X n) :=
    fun n hn => (CochainComplex.isStrictlyGE_iff I b).mp hIb n hn
  let u := (restrictPushforwardComplexAdjunction j).homEquiv P I q
  let B := CochainComplex.mappingCone u
  let α := (pushforwardDerivedHomEquiv j A I b hbI hi).symm (φ ≫ (toDerived U).map q)
  obtain ⟨M, r, hM, hr, hkill⟩ := h A B hA (b-1) hCb hCqc hzC
    (α ≫ (toDerived X).map (CochainComplex.mappingCone.inr u))
  let := hr
  obtain ⟨γ, hγ⟩ := Triangle.coyoneda_exact₂ _ (mappingConeTriangle_distinguished u)
    ((toDerived X).map r ≫ α) (by
      change ((toDerived X).map r ≫ α) ≫
        (toDerived X).map (CochainComplex.mappingCone.inr u) = 0
      simpa only [Category.assoc] using hkill)
  change (toDerived X).obj M ⟶ (toDerived X).obj P at γ
  change (toDerived X).map r ≫ α = γ ≫ (toDerived X).map u at hγ
  have hlocal : (toDerived U).map ((restrict j).map r) ≫ φ = restrictDerivedHom j γ := by
    apply (cancel_mono ((toDerived U).map q)).mp
    have hh := congrArg (pushforwardDerivedHomEquiv j M I b hbI hi) hγ
    rw [pushforwardDerivedHomEquiv_precomp, pushforwardDerivedHomEquiv_precomp] at hh
    have hu : pushforwardDerivedHomEquiv j P I b hbI hi ((toDerived X).map u) =
        (toDerived U).map q := by
      rw [pushforwardDerivedHomEquiv_map]
      exact congrArg ((toDerived U).map)
        (((restrictPushforwardComplexAdjunction j).homEquiv P I).symm_apply_apply q)
    rw [hu, AddEquiv.apply_symm_apply] at hh
    simpa only [restrictDerivedHom_map, Category.assoc] using hh
  obtain ⟨N, s, a, hs, ha⟩ := toDerived_right_fraction γ
  let := hs
  refine ⟨N, s ≫ r, a, (locallyPerfect_iff_of_quasiIso s).mpr hM, ?_, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · have hh := congrArg (restrictDerivedHom j) ha
    simp only [restrictDerivedHom_comp, restrictDerivedHom_map] at hh
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hlocal]
    exact hh

/-- Genuine supported denominators kill every original map whose open restriction is zero.
The target need only be lower-bounded with QC homology, not perfect or supported globally. -/
lemma exists_denominator_of_restrictDerivedHom_zero [QuasiCompact j]
    (h : HasSupportedQCDenominators j) {A B : Complex X}
    (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (α : (toDerived X).obj A ⟶ (toDerived X).obj B)
    (hzero : restrictDerivedHom j α = 0) :
    ∃ (M : Complex X) (q : M ⟶ A), locallyPerfect X M ∧
      QuasiIso ((restrict j).map q) ∧ (toDerived X).map q ≫ α = 0 := by
  obtain ⟨I, q, hIb, hi, hq, hCqc, hCb, hzC⟩ := exists_restrictionUnitCone_model j B b hB
  let := hq
  have hbI : ∀ n, n < b → IsZero (I.X n) :=
    fun n hn => (CochainComplex.isStrictlyGE_iff I b).mp hIb n hn
  let u := (restrictPushforwardComplexAdjunction j).homEquiv B I q
  have hαu : α ≫ (toDerived X).map u = 0 := by
    apply (pushforwardDerivedHomEquiv j A I b hbI hi).injective
    rw [pushforwardDerivedHomEquiv_precomp, hzero, zero_comp, map_zero]
  obtain ⟨γ, hγ⟩ := Triangle.coyoneda_exact₂ _
    (DerivedCategory.mappingCocone_triangle_distinguished u) α hαu
  change (toDerived X).obj A ⟶ (toDerived X).obj (CochainComplex.mappingCocone u) at γ
  change α = γ ≫ (toDerived X).map (CochainComplex.mappingCocone.fst u) at hγ
  have hFqc (n : ℤ) : ((CochainComplex.mappingCocone u).homology n).IsQuasicoherent :=
    quasicoherent_homology_shift _ hCqc (-1) n
  have hFb : (CochainComplex.mappingCocone u).IsGE b := by
    let := hCb
    exact CochainComplex.isGE_shift (CochainComplex.mappingCone u) (b-1) (-1) b (by omega)
  have hFzero : IsZero ((toDerived U).obj ((restrict j).obj (CochainComplex.mappingCocone u))) :=
    isZero_restrict_shift_of_isZero j _ hzC (-1)
  obtain ⟨M,r,hM,hr,hkill⟩ := h A _ hA b hFb hFqc hFzero γ
  exact ⟨M,r,hM,hr,by rw [hγ, ← Category.assoc, hkill, zero_comp]⟩

/-- Original equality on the open is equalized by one genuine locally weak perfect denominator. -/
lemma exists_denominator_of_restrictDerivedHom_eq [QuasiCompact j]
    (h : HasSupportedQCDenominators j) {A B : Complex X}
    (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (α β : (toDerived X).obj A ⟶ (toDerived X).obj B)
    (heq : restrictDerivedHom j α = restrictDerivedHom j β) :
    ∃ (M : Complex X) (q : M ⟶ A), locallyPerfect X M ∧
      QuasiIso ((restrict j).map q) ∧ (toDerived X).map q ≫ α = (toDerived X).map q ≫ β := by
  have hz : restrictDerivedHom j (α-β) = 0 := by
    simpa only [restrictDerivedHom, Functor.map_sub, Preadditive.comp_sub,
      Preadditive.sub_comp] using sub_eq_zero.mpr heq
  obtain ⟨M,q,hM,hq,hkill⟩ := exists_denominator_of_restrictDerivedHom_zero j h hA b hB (α-β) hz
  exact ⟨M,q,hM,hq,sub_eq_zero.mp (by simpa only [Preadditive.comp_sub] using hkill)⟩

end OpenDerivedImage
end Quillen.PerfectComplexes
