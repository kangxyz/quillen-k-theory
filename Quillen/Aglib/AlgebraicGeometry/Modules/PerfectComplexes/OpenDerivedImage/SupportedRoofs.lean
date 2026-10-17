/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Homology
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.SourceSupportedDenominators
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

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
    {A P : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) (hP : locallyPerfect X P)
    (hzA : IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj A)))
    (φ : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj A) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P)) :
    ∃ (N : CochainComplex X.Modules ℤ) (q : N ⟶ A) (g : N ⟶ P), locallyPerfect X N ∧
      QuasiIso ((restrict j).map q) ∧
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) ≫ φ =
        (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map g) ∧
      IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj N)) := by
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
  let α := (pushforwardDerivedHomEquiv j A I b hbI hi).symm
    (φ ≫ (DerivedCategory.Q (C := U.Modules)).map q)
  let := hCb
  obtain ⟨M, r, hM, hr, hzM, hkill⟩ := exists_source_supported_denominator j T hT hA (b-1)
    hCqc hzC hzA (α ≫ (DerivedCategory.Q (C := X.Modules)).map (CochainComplex.mappingCone.inr u))
  let := hr
  obtain ⟨γ, hγ⟩ := Triangle.coyoneda_exact₂ _ (DerivedCategory.mappingCone_triangle_distinguished
    u)
    ((DerivedCategory.Q (C := X.Modules)).map r ≫ α) (by
      change ((DerivedCategory.Q (C := X.Modules)).map r ≫ α) ≫
        (DerivedCategory.Q (C := X.Modules)).map (CochainComplex.mappingCone.inr u) = 0
      simpa only [Category.assoc] using hkill)
  change (DerivedCategory.Q (C := X.Modules)).obj M ⟶
    (DerivedCategory.Q (C := X.Modules)).obj P at γ
  change (DerivedCategory.Q (C := X.Modules)).map r ≫ α = γ ≫
    (DerivedCategory.Q (C := X.Modules)).map u at hγ
  have hlocal : (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map r) ≫ φ
    = restrictDerivedHom j γ := by
    apply (cancel_mono ((DerivedCategory.Q (C := U.Modules)).map q)).mp
    have hh := congrArg (pushforwardDerivedHomEquiv j M I b hbI hi) hγ
    rw [pushforwardDerivedHomEquiv_precomp, pushforwardDerivedHomEquiv_precomp] at hh
    have hu : pushforwardDerivedHomEquiv j P I b hbI hi ((DerivedCategory.Q (C := X.Modules)).map u)
      =
        (DerivedCategory.Q (C := U.Modules)).map q := by
      rw [pushforwardDerivedHomEquiv_map]
      exact congrArg ((DerivedCategory.Q (C := U.Modules)).map)
        (((restrictPushforwardComplexAdjunction j).homEquiv P I).symm_apply_apply q)
    rw [hu, AddEquiv.apply_symm_apply] at hh
    simpa only [restrictDerivedHom_map, Category.assoc] using hh
  obtain ⟨N, s, hDenIso1, a, hFac1⟩ := DerivedCategory.right_fac γ
  have hs : QuasiIso s :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hDenIso1
  have ha : DerivedCategory.Q.map s ≫ (γ) = DerivedCategory.Q.map a := by
    let := hDenIso1
    rw [hFac1, IsIso.hom_inv_id_assoc]
  let := hs
  refine ⟨N, s ≫ r, a, (locallyPerfect_iff_of_quasiIso s).mpr hM, ?_, ?_, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · have hh := congrArg (restrictDerivedHom j) ha
    simp only [restrictDerivedHom_comp, restrictDerivedHom_map] at hh
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hlocal]
    exact hh
  · exact hzM.of_iso (asIso ((DerivedCategory.Q (C := T.toScheme.Modules)).map
      ((restrict T.ι).map s)))

/-- Original roofs in the fixed-support full subcategories. All arrows remain
actual global chain maps and the denominator is weak after original restriction. -/
def HasSupportedDerivedRoofs {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : X.Opens) : Prop :=
  ∀ (A B : CochainComplex X.Modules ℤ), locallyPerfect X A → locallyPerfect X B →
    IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj A)) →
    IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj B)) →
    ∀ φ : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj A) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B),
      ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A) (g : M ⟶ B), locallyPerfect X M ∧
        QuasiIso ((restrict j).map q) ∧
        (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q) ≫ φ =
          (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map g) ∧
        IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj M))

/-- Genuine fixed-support roofs for arbitrary compact open immersions into qcqs schemes. -/
lemma qcqs_hasSupportedDerivedRoofs {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X)) :
    HasSupportedDerivedRoofs j T := by
  intro A B hA hB hzA _ φ
  exact exists_source_supported_derived_roof j T hT hA hB hzA φ

end Quillen.PerfectComplexes.OpenDerivedImage
