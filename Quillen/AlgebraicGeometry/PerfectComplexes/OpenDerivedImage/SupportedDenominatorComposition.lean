/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.SupportedQCDenominators
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalSupportedDensity

/-! # Supported denominator transitivity via actual supported cone retracts -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves

lemma isZero_restrict_opensRange_of_isZero {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {E : Complex X}
    (hz : IsZero ((toDerived U).obj ((restrict j).obj E))) :
    IsZero ((toDerived j.opensRange.toScheme).obj ((restrict j.opensRange.ι).obj E)) := by
  rw [← isZero_toDerived_restrict_iff_of_isIso j.isoOpensRange.hom]
  let c := restrictCompIso j.isoOpensRange.hom j.opensRange.ι ≪≫
    eqToIso (restrict_congr j.isoOpensRange_hom_ι)
  exact hz.of_iso ((toDerived U).mapIso (c.app E))

lemma isZero_restrict_of_isZero_opensRange {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {E : Complex X}
    (hz : IsZero ((toDerived j.opensRange.toScheme).obj ((restrict j.opensRange.ι).obj E))) :
    IsZero ((toDerived U).obj ((restrict j).obj E)) := by
  let c := restrictCompIso j.isoOpensRange.hom j.opensRange.ι ≪≫
    eqToIso (restrict_congr j.isoOpensRange_hom_ι)
  exact (isZero_toDerived_restrict_of_isZero j.isoOpensRange.hom hz).of_iso
    ((toDerived U).mapIso (c.app E)).symm

namespace OpenDerivedImage

/-- Supported denominators compose across nested compact opens. The cone of
the first local denominator is genuinely extended with support; its original
factorization is lifted by roofs on the second open, then the actual global
perfect fiber and the original QC null-map bridge finish the construction. -/
lemma hasSupportedQCDenominators_comp {Z U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U] [CompactSpace Z]
    (i : Z ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (h₁ : HasSupportedQCDenominators i) (h₂ : HasSupportedQCDenominators j) :
    HasSupportedQCDenominators (i ≫ j) := by
  let c := restrictCompIso i j
  let V := (i ≫ j).opensRange
  have hV : IsCompact (V : Set X) := isCompact_range (i ≫ j).continuous
  intro A B hA b hb hB hzB α
  let := hb
  have hBU : ((restrict j).obj B).IsGE b := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    exact (B.exactAt_of_isGE b n hn).map (Scheme.Modules.restrictFunctor j)
  have hzBU : IsZero ((toDerived Z).obj ((restrict i).obj ((restrict j).obj B))) :=
    hzB.of_iso ((toDerived Z).mapIso (c.app B))
  obtain ⟨N, q, hN, hq, hqα⟩ := h₁ ((restrict j).obj A) ((restrict j).obj B)
    (locallyPerfect_restrict j hA) b hBU (Affine.quasicoherent_homology_restrict j B hB)
    hzBU (restrictDerivedHom j α)
  let E := CochainComplex.mappingCone q
  have hE : locallyPerfect U E := locallyPerfect_mappingCone hN (locallyPerfect_restrict j hA) q
  have hzEi : IsZero ((toDerived Z).obj ((restrict i).obj E)) := by
    exact (Triangle.isZero₃_of_isIso₁ _ (mappingConeTriangle_distinguished ((restrict i).map q)) (by
      change IsIso ((toDerived Z).map ((restrict i).map q))
      infer_instance)).of_iso
        ((toDerived Z).mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso q
          (Scheme.Modules.restrictFunctor i)))
  have hzE : IsZero ((toDerived (j ⁻¹ᵁ V).toScheme).obj ((restrict (j ⁻¹ᵁ V).ι).obj E)) := by
    have h := isZero_restrict_opensRange_of_isZero i hzEi
    have hpre : j ⁻¹ᵁ V = i.opensRange := by
      dsimp [V]
      rw [Scheme.Hom.opensRange_comp, Scheme.Hom.preimage_image_eq]
    rw [hpre]
    exact h
  obtain ⟨C, D, hC, _, ⟨eC⟩, hzCV⟩ :=
    locallyPerfect_exists_global_supported_perfect_complement_of_openImmersion j E hE V hV hzE
  let r₀ : Retract E (E ⊞ D) :=
    { i := biprod.inl, r := biprod.fst, retract := biprod.inl_fst }
  let r := (r₀.map (toDerived U)).trans (Retract.ofIso eC.symm)
  have hzC : IsZero ((toDerived Z).obj ((restrict (i ≫ j)).obj C)) :=
    isZero_restrict_of_isZero_opensRange (i ≫ j) hzCV
  obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₂ _ (mappingConeTriangle_distinguished q)
    (restrictDerivedHom j α) hqα
  change restrictDerivedHom j α = (toDerived U).map (CochainComplex.mappingCone.inr q) ≫ γ at hγ
  let β := (toDerived U).map (CochainComplex.mappingCone.inr q) ≫ r.i
  let η := r.r ≫ γ
  have hβη : β ≫ η = restrictDerivedHom j α := by
    dsimp [β, η]
    rw [Category.assoc, ← Category.assoc r.i r.r γ, r.retract, Category.id_comp, ← hγ]
  obtain ⟨A', a, g, hA', ha, hg⟩ :=
    hasDerivedRoofs_of_supportedQCDenominators j h₂ A C hA hC β
  let P := CochainComplex.mappingCocone g
  let f := CochainComplex.mappingCocone.fst g
  have hP : locallyPerfect X P := locallyPerfect_mappingCocone hA' hC g
  have hfZ : QuasiIso ((restrict (i ≫ j)).map f) :=
    quasiIso_restrict_mappingCocone_fst_of_isZero (i ≫ j) g hzC
  have haZ : QuasiIso ((restrict (i ≫ j)).map a) := by
    have hui : QuasiIso ((restrict i).map ((restrict j).map a)) := inferInstance
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (c.app A') (c.app A) (c.hom.naturality a).symm)).mp hui
  have hfg : (toDerived X).map f ≫ (toDerived X).map g = 0 :=
    comp_distTriang_mor_zero₁₂ _ (DerivedCategory.mappingCocone_triangle_distinguished g)
  have hfgU := congrArg (restrictDerivedHom j) hfg
  simp only [restrictDerivedHom_comp, restrictDerivedHom_map] at hfgU
  have hz : restrictDerivedHom j (0 : (toDerived X).obj P ⟶ (toDerived X).obj C) = 0 := by simp
    [restrictDerivedHom]
  rw [hz] at hfgU
  have hnull : restrictDerivedHom j ((toDerived X).map (f ≫ a) ≫ α) = 0 := by
    simp only [Functor.map_comp, restrictDerivedHom_comp, restrictDerivedHom_map]
    rw [← hβη, Category.assoc, ← Category.assoc ((toDerived U).map ((restrict j).map a)), hg]
    rw [← Category.assoc, hfgU, zero_comp]
  obtain ⟨M, s, hM, hs, hkill⟩ := exists_denominator_of_restrictDerivedHom_zero j h₂
    hP b hB ((toDerived X).map (f ≫ a) ≫ α) hnull
  have hsZ : QuasiIso ((restrict (i ≫ j)).map s) := by
    have hui : QuasiIso ((restrict i).map ((restrict j).map s)) := inferInstance
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (c.app M) (c.app P) (c.hom.naturality s).symm)).mp hui
  refine ⟨M, s ≫ f ≫ a, hM, ?_, ?_⟩
  · simp only [Functor.map_comp]
    infer_instance
  · simpa only [Functor.map_comp, Category.assoc] using hkill

end OpenDerivedImage
end Quillen.PerfectComplexes
