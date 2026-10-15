/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.SourceSupportedDenominators

/-! # Original global derived roofs with prescribed source support -/
@[expose] public section

open HomologicalComplex


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] Affine.standardDerivedSheaves

/-- A roof for an arbitrary original local derived arrow retains the vanishing
of its original source on any prescribed compact open. The target need not vanish there. -/
lemma exists_source_supported_derived_roof {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A P : Complex X} (hA : locallyPerfect X A) (hP : locallyPerfect X P)
    (hzA : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A)))
    (φ : (toDerived U).obj ((restrict j).obj A) ⟶ (toDerived U).obj ((restrict j).obj P)) :
    ∃ (N : Complex X) (q : N ⟶ A) (g : N ⟶ P), locallyPerfect X N ∧
      QuasiIso ((restrict j).map q) ∧
      (toDerived U).map ((restrict j).map q) ≫ φ = (toDerived U).map ((restrict j).map g) ∧
      IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj N)) := by
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
  let := hCb
  obtain ⟨M, r, hM, hr, hzM, hkill⟩ := exists_source_supported_denominator j T hT hA (b-1)
    hCqc hzC hzA (α ≫ (toDerived X).map (CochainComplex.mappingCone.inr u))
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
  refine ⟨N, s ≫ r, a, (locallyPerfect_iff_of_quasiIso s).mpr hM, ?_, ?_, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · have hh := congrArg (restrictDerivedHom j) ha
    simp only [restrictDerivedHom_comp, restrictDerivedHom_map] at hh
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hlocal]
    exact hh
  · exact hzM.of_iso (asIso ((toDerived T.toScheme).map ((restrict T.ι).map s)))

/-- Original roofs in the fixed-support full subcategories. All arrows remain
actual global chain maps and the denominator is weak after original restriction. -/
def HasSupportedDerivedRoofs {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : X.Opens) : Prop :=
  ∀ (A B : Complex X), locallyPerfect X A → locallyPerfect X B →
    IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A)) →
    IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj B)) →
    ∀ φ : (toDerived U).obj ((restrict j).obj A) ⟶ (toDerived U).obj ((restrict j).obj B),
      ∃ (M : Complex X) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect X M ∧
        QuasiIso ((restrict j).map q) ∧
        (toDerived U).map ((restrict j).map q) ≫ φ = (toDerived U).map ((restrict j).map g) ∧
        IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M))

/-- Genuine fixed-support roofs for arbitrary compact open immersions into qcqs schemes. -/
lemma qcqs_hasSupportedDerivedRoofs {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X)) :
    HasSupportedDerivedRoofs j T := by
  intro A B hA hB hzA _ φ
  exact exists_source_supported_derived_roof j T hT hA hB hzA φ

end Quillen.PerfectComplexes.OpenDerivedImage
