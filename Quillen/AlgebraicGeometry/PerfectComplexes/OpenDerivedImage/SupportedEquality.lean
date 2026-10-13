/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.SourceSupportedDenominators

/-! # Fixed-source-support denominators for original local equalities -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] Affine.standardDerivedSheaves

/-- Local nullity of an original derived map is cleared by a genuine denominator
which retains the source support. The arbitrary lower-bounded QC target need
not vanish on either open. -/
lemma exists_source_supported_denominator_of_restrictDerivedHom_zero {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A B : Complex X} (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (hzA : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A)))
    (α : (toDerived X).obj A ⟶ (toDerived X).obj B)
    (hzero : restrictDerivedHom j α = 0) :
    ∃ (M : Complex X) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso ((restrict j).map q) ∧
      IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M)) ∧ (toDerived X).map q ≫ α = 0 := by
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
  let := hFb
  obtain ⟨M,r,hM,hr,hzM,hkill⟩ := exists_source_supported_denominator j T hT hA b hFqc hFzero hzA γ
  exact ⟨M,r,hM,hr,hzM,by rw [hγ, ← Category.assoc, hkill, zero_comp]⟩

/-- Original local equality has one source-supported actual global denominator. -/
lemma exists_source_supported_denominator_of_restrictDerivedHom_eq {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A B : Complex X} (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (hzA : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A)))
    (α β : (toDerived X).obj A ⟶ (toDerived X).obj B)
    (heq : restrictDerivedHom j α = restrictDerivedHom j β) :
    ∃ (M : Complex X) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso ((restrict j).map q) ∧
      IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M)) ∧
      (toDerived X).map q ≫ α = (toDerived X).map q ≫ β := by
  have hz : restrictDerivedHom j (α-β) = 0 := by
    simpa only [restrictDerivedHom, Functor.map_sub, Preadditive.comp_sub,
      Preadditive.sub_comp] using sub_eq_zero.mpr heq
  obtain ⟨M,q,hM,hq,hzM,hkill⟩ := exists_source_supported_denominator_of_restrictDerivedHom_zero
    j T hT hA b hB hzA (α-β) hz
  exact ⟨M,q,hM,hq,hzM,sub_eq_zero.mp (by simpa only [Preadditive.comp_sub] using hkill)⟩

/-- Equality of the original restricted derived chain maps yields an actual
global chain homotopy after a source-supported perfect denominator. -/
lemma exists_source_supported_homotopy_of_restrict_derived_eq {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A B : Complex X} (hA : locallyPerfect X A) (b : ℤ) [B.IsGE b]
    (hB : ∀ n, (B.homology n).IsQuasicoherent)
    (hzA : IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj A)))
    (f g : A ⟶ B)
    (heq : (toDerived U).map ((restrict j).map f) = (toDerived U).map ((restrict j).map g)) :
    ∃ (M : Complex X) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso ((restrict j).map q) ∧
      IsZero ((toDerived T.toScheme).obj ((restrict T.ι).obj M)) ∧
      Nonempty (Homotopy (q ≫ f) (q ≫ g)) := by
  obtain ⟨P,q,hP,hq,hzP,hfg⟩ := exists_source_supported_denominator_of_restrictDerivedHom_eq
    j T hT hA b hB hzA ((toDerived X).map f) ((toDerived X).map g)
    (by simpa only [restrictDerivedHom_map] using heq)
  let : HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
  have he : DerivedCategory.Q.{u+1}.map (q ≫ f) = DerivedCategory.Q.{u+1}.map (q ≫ g) := by
    change (toDerived X).map (q ≫ f) = (toDerived X).map (q ≫ g)
    simpa only [Functor.map_comp] using hfg
  obtain ⟨M,s,hs,⟨H⟩⟩ :=
    Quillen.CochainComplex.exists_pre_quasiIso_homotopy_of_derived_eq (q ≫ f) (q ≫ g) he
  refine ⟨M,s ≫ q,(locallyPerfect_iff_of_quasiIso s).mpr hP,?_,?_,?_⟩
  · rw [(restrict j).map_comp]
    infer_instance
  · exact hzP.of_iso (asIso ((toDerived T.toScheme).map ((restrict T.ι).map s)))
  · exact ⟨by simpa only [Category.assoc] using H⟩

end Quillen.PerfectComplexes.OpenDerivedImage
