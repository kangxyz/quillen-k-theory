/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenQCTargetRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRestrictionRoofs

/-! # Genuine affine supported denominators for original QC-homology targets -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] standardDerivedModules standardDerivedSheaves

lemma exists_perfect_denominator_of_lowerBounded_qc_supported_target
    (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {A B : Complex (Spec R)} (hA : locallyPerfect (Spec R) A) (b : ℤ) [B.IsGE b]
    (hBqc : ∀ n, (B.homology n).IsQuasicoherent)
    (hzB : IsZero ((toDerived W.toScheme).obj ((restrict W.ι).obj B)))
    (α : (toDerived (Spec R)).obj A ⟶ (toDerived (Spec R)).obj B) :
    ∃ (M : Complex (Spec R)) (q : M ⟶ A), locallyPerfect (Spec R) M ∧
      QuasiIso ((restrict W.ι).map q) ∧ (toDerived (Spec R)).map q ≫ α = 0 ∧
      ∀ (Z : (Spec R).Opens), IsCompact (Z : Set (Spec R)) →
        IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj A)) →
        IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj M)) := by
  obtain ⟨A₀, hA₀, ⟨eA⟩⟩ := locallyPerfect_exists_moduleStrictPerfect_representative R hA
  obtain ⟨B₀, hB₀, ⟨eB⟩⟩ := exists_lowerBounded_module_representative B b hBqc
  let T : (Spec R).Opens := ⊤
  let : IsIso T.ι := inferInstanceAs (IsIso (Spec R).topIso.hom)
  let β := eA.hom ≫ α ≫ eB.inv
  obtain ⟨P, hP, t, g, ht, hg, _⟩ :=
    exists_quasiCompact_open_module_roof_preserving_source_support R T isCompact_univ hA₀ b
      (restrictDerivedHom T.ι β)
  have htg : QuasiIso ((associatedComplex R).map t) :=
    (quasiIso_restrict_iff_of_isIso T.ι _).mp ht
  have hβ : (toDerived (Spec R)).map ((associatedComplex R).map t) ≫ β =
      (toDerived (Spec R)).map ((associatedComplex R).map g) := by
    apply restrictDerivedHom_injective_of_isIso T.ι
    simpa only [restrictDerivedHom_comp, restrictDerivedHom_map] using hg
  let eP := asIso ((toDerived (Spec R)).map ((associatedComplex R).map t)) ≪≫ eA
  have hgP : eP.hom ≫ α = (toDerived (Spec R)).map ((associatedComplex R).map g) ≫ eB.hom := by
    rw [← hβ]
    simp only [eP, Iso.trans_hom, asIso_hom, β, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hB₀W : IsZero ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj
    B₀))) :=
    hzB.of_iso (restrictDerivedIso W.ι eB)
  obtain ⟨sW, hsW⟩ := exists_finite_principal_cover R W hW
  have hB₀s (r : R) (hr : r ∈ sW) :
      IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj B₀)) := by
    apply isZero_localize_of_isZero_restrict_associated R W B₀ hB₀W r
    rw [← hsW]
    exact Quillen.SheafCohomology.basicOpen_le_principalUnion R hr
  obtain ⟨P', hP', q', hqg, hqW, hsupport⟩ :=
    exists_perfect_denominator_preserving_source_support R sW hP hB₀s (DerivedCategory.Q.map g)
  have hq'W : QuasiIso ((restrict W.ι).map ((associatedComplex R).map q')) :=
    quasiIso_restrict_associated_of_principalUnion R W sW hsW q' hqW
  have hzqg : (toDerived (Spec R)).map ((associatedComplex R).map q') ≫
      (toDerived (Spec R)).map ((associatedComplex R).map g) = 0 := by
    have hz : DerivedCategory.Q.map (q' ≫ g) = DerivedCategory.Q.map (0 : P' ⟶ B₀) := by
      simpa only [Functor.map_comp, Functor.map_zero] using hqg
    have := isKProjective_of_moduleStrictPerfect R hP'
    let H := Quillen.CochainComplex.homotopyOfDerivedEqOfIsKProjective (q' ≫ g) 0 hz
    have heq := toDerived_map_eq_of_homotopy ((tilde.functor R).mapHomotopy H)
    simpa only [associatedComplex, Functor.map_comp, Functor.map_zero] using heq
  let δ := (toDerived (Spec R)).map ((associatedComplex R).map q') ≫ eP.hom
  obtain ⟨M, s, q, hs, hq⟩ := toDerived_right_fraction δ
  have hM : locallyPerfect (Spec R) M :=
    (locallyPerfect_iff_of_quasiIso s).mpr (locallyPerfect_of_strictPerfect
      (strictPerfect_associated R hP'))
  have hqr := congrArg (restrictDerivedHom W.ι) hq
  simp only [δ, restrictDerivedHom_comp, restrictDerivedHom_map] at hqr
  have hweak : QuasiIso ((restrict W.ι).map q) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso W.toScheme.Modules _).mp
    change IsIso ((toDerived W.toScheme).map ((restrict W.ι).map q))
    rw [← hqr]
    change IsIso ((toDerived W.toScheme).map ((restrict W.ι).map s) ≫
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map q')) ≫
        (restrictDerivedIso W.ι eP).hom)
    infer_instance
  refine ⟨M, q, hM, hweak, ?_, ?_⟩
  · rw [← hq]
    change (_ ≫ (_ ≫ eP.hom)) ≫ α = 0
    rw [Category.assoc, Category.assoc, hgP]
    rw [← Category.assoc ((toDerived (Spec R)).map ((associatedComplex R).map q'))
      ((toDerived (Spec R)).map ((associatedComplex R).map g)), hzqg, zero_comp, comp_zero]
  · intro Z hZ hz
    have hPZ : IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj ((associatedComplex R).obj
      P))) :=
      hz.of_iso (restrictDerivedIso Z.ι eP)
    obtain ⟨sZ, hsZ⟩ := exists_finite_principal_cover R Z hZ
    have hpZ : IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj ((associatedComplex R).obj
      P'))) := by
      apply isZero_restrict_associated_of_principalUnion R Z sZ hsZ
      intro r hr
      apply hsupport r
      apply isZero_localize_of_isZero_restrict_associated R Z P hPZ r
      rw [← hsZ]
      exact Quillen.SheafCohomology.basicOpen_le_principalUnion R hr
    exact hpZ.of_iso (asIso ((toDerived Z.toScheme).map ((restrict Z.ι).map s)))

/-- The original morphism factors through an actual global perfect complex
vanishing on the original compact open. Its first arrow is an actual cone inclusion. -/
lemma exists_perfect_factorization_of_lowerBounded_qc_supported_target
    (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {A B : Complex (Spec R)} (hA : locallyPerfect (Spec R) A) (b : ℤ) [B.IsGE b]
    (hBqc : ∀ n, (B.homology n).IsQuasicoherent)
    (hzB : IsZero ((toDerived W.toScheme).obj ((restrict W.ι).obj B)))
    (α : (toDerived (Spec R)).obj A ⟶ (toDerived (Spec R)).obj B) :
    ∃ (C : Complex (Spec R)) (i : A ⟶ C)
      (γ : (toDerived (Spec R)).obj C ⟶ (toDerived (Spec R)).obj B),
      locallyPerfect (Spec R) C ∧
      IsZero ((toDerived W.toScheme).obj ((restrict W.ι).obj C)) ∧
      (toDerived (Spec R)).map i ≫ γ = α := by
  obtain ⟨M, q, hM, hq, hqα, _⟩ :=
    exists_perfect_denominator_of_lowerBounded_qc_supported_target R W hW hA b hBqc hzB α
  obtain ⟨γ, hγ⟩ := CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂ _
    (mappingConeTriangle_distinguished q) α hqα
  refine ⟨CochainComplex.mappingCone q, CochainComplex.mappingCone.inr q, γ,
    locallyPerfect_mappingCone hM hA q, ?_, hγ.symm⟩
  exact (CategoryTheory.Pretriangulated.Triangle.isZero₃_of_isIso₁ _
    (mappingConeTriangle_distinguished ((restrict W.ι).map q)) (by
      change IsIso ((toDerived W.toScheme).map ((restrict W.ι).map q))
      infer_instance)).of_iso
      ((toDerived W.toScheme).mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso q
        (Scheme.Modules.restrictFunctor W.ι)))

/-- The original denominator theorem along an arbitrary compact open immersion
into Spec, with the same global morphism and every source support condition. -/
lemma exists_perfect_denominator_of_lowerBounded_qc_supported_target_immersion
    (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R)
    [IsOpenImmersion j] [CompactSpace U]
    {A B : Complex (Spec R)} (hA : locallyPerfect (Spec R) A) (b : ℤ) [B.IsGE b]
    (hBqc : ∀ n, (B.homology n).IsQuasicoherent)
    (hzB : IsZero ((toDerived U).obj ((restrict j).obj B)))
    (α : (toDerived (Spec R)).obj A ⟶ (toDerived (Spec R)).obj B) :
    ∃ (M : Complex (Spec R)) (q : M ⟶ A), locallyPerfect (Spec R) M ∧
      QuasiIso ((restrict j).map q) ∧ (toDerived (Spec R)).map q ≫ α = 0 ∧
      ∀ (Z : (Spec R).Opens), IsCompact (Z : Set (Spec R)) →
        IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj A)) →
        IsZero ((toDerived Z.toScheme).obj ((restrict Z.ι).obj M)) := by
  let W := j.opensRange
  let e := j.isoOpensRange.symm
  let c : restrict j ⋙ restrict e.hom ≅ restrict W.ι :=
    restrictCompIso e.hom j ≪≫ eqToIso (restrict_congr j.isoOpensRange_inv_comp)
  have hzW : IsZero ((toDerived W.toScheme).obj ((restrict W.ι).obj B)) :=
    (isZero_toDerived_restrict_of_isZero e.hom hzB).of_iso
      ((toDerived W.toScheme).mapIso (c.app B)).symm
  obtain ⟨M, q, hM, hq, hqα, hs⟩ :=
    exists_perfect_denominator_of_lowerBounded_qc_supported_target R W
      (isCompact_range j.continuous) hA b hBqc hzW α
  have hq' : QuasiIso ((restrict e.hom).map ((restrict j).map q)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (c.app M) (c.app A) (c.hom.naturality q).symm)).mpr hq
  exact ⟨M, q, hM, (quasiIso_restrict_iff_of_isIso e.hom _).mp hq', hqα, hs⟩

end Quillen.PerfectComplexes.Affine
