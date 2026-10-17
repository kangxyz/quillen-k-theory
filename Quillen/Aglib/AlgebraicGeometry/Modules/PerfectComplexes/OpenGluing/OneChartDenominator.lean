/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.QCSupportedDenominators
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenGluing.ImmersionDerivedTarget
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.DerivedHom.Nilpotence
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-! # Genuine global supported denominators across one affine chart

A local affine annihilator glues with the original identity on the open where
the target is zero. Actual Mayer–Vietoris kills the remaining global map;
local nullity is used only with this explicit zero-target condition.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves

lemma derivedHom_eq_zero_of_target_zero_and_cover
    {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {A B : CochainComplex X.Modules ℤ} (hzB : IsZero
      ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B)))
    (α : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B)
    (hk : restrictDerivedHom k α = 0) : α = 0 := by
  have h := derivedHom_comp_eq_zero_of_openSquare (pullback.fst j k) (pullback.snd j k) j k
    pullback.condition
    (by intro x hx; rw [IsOpenImmersion.range_pullbackFst]; exact hx)
    (by intro x hx; rw [IsOpenImmersion.range_pullbackSnd]; exact hx)
    hcover α (𝟙 ((DerivedCategory.Q (C := X.Modules)).obj B)) (hzB.eq_of_tgt _ _) hk
      (hzB.eq_of_tgt _ _)
  simpa only [Category.comp_id] using h

/-- With one affine chart outside the zero-target open, the original global
map admits an actual perfect source denominator weak on that original open. -/
lemma exists_perfect_denominator_across_spec_of_qc_target
    (R : CommRingCat.{u}) {U X : Scheme.{u}} [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {A B : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) (n : ℤ) [B.IsGE n]
    (hBqc : ∀ m, (B.homology m).IsQuasicoherent)
    (hzB : IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B)))
    (α : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B) :
    ∃ (P : CochainComplex X.Modules ℤ) (q : P ⟶ A), locallyPerfect X P ∧
      QuasiIso ((restrict j).map q) ∧ (DerivedCategory.Q (C := X.Modules)).map q ≫ α = 0 := by
  let a := pullback.fst j k
  let b := pullback.snd j k
  let Q := DerivedCategory.Q (C := (pullback j k).Modules)
  let c := openSquareRestrictIso b a k j pullback.condition.symm
  have hBn : ((restrict k).obj B).IsGE n := by
    rw [CochainComplex.isGE_iff]
    intro m hm
    exact (B.exactAt_of_isGE n m hm).map (Scheme.Modules.restrictFunctor k)
  have hzBb : IsZero (Q.obj ((restrict b).obj ((restrict k).obj B))) :=
    (isZero_toDerived_restrict_of_isZero a hzB).of_iso (Q.mapIso (c.app B))
  obtain ⟨C, q, hC, hq, hqα, _⟩ :=
    Affine.exists_perfect_denominator_of_lowerBounded_qc_supported_target_immersion R b
      (locallyPerfect_restrict k hA) n (Affine.quasicoherent_homology_restrict k B hBqc)
      hzBb (restrictDerivedHom k α)
  let e := (Q.mapIso (c.app A)).symm ≪≫ (asIso (Q.map ((restrict b).map q))).symm
  have he : restrictDerivedHom a (𝟙 ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj A)))
    =
      e.hom ≫ restrictDerivedHom b ((DerivedCategory.Q (C := (Spec R).Modules)).map q) ≫ Q.map
        (c.hom.app A) := by
    rw [restrictDerivedHom_id, restrictDerivedHom_map]
    change 𝟙 _ = (Q.map (c.inv.app A) ≫ inv (Q.map ((restrict b).map q))) ≫
      Q.map ((restrict b).map q) ≫ Q.map (c.hom.app A)
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← Q.map_comp, c.inv_hom_id_app]
    exact (CategoryTheory.Functor.map_id _ _).symm
  obtain ⟨P, hP, u, v, d, hu, hv, _⟩ :=
    OpenHomotopyGluing.exists_perfect_glue_of_derived_target_immersions j k hcover
      (locallyPerfect_restrict j hA) hC e (𝟙 _) ((DerivedCategory.Q
        (C := (Spec R).Modules)).map q) he
  have hdj : QuasiIso ((restrict j).map d) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules _).mp
    have : IsIso (u.hom ≫ (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map d))
      := by rw [hu]; infer_instance
    exact IsIso.of_isIso_comp_left u.hom _
  refine ⟨P, d, hP, hdj, ?_⟩
  apply derivedHom_eq_zero_of_target_zero_and_cover j k hcover hzB
  rw [restrictDerivedHom_comp, restrictDerivedHom_map]
  apply (cancel_epi v.hom).mp
  rw [← Category.assoc, hv, hqα, comp_zero]

/-- The same one-chart geometry gives actual supported factorization through
the original cone of the constructed denominator. -/
lemma exists_perfect_factorization_across_spec_of_qc_target
    (R : CommRingCat.{u}) {U X : Scheme.{u}} [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {A B : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) (n : ℤ) [B.IsGE n]
    (hBqc : ∀ m, (B.homology m).IsQuasicoherent)
    (hzB : IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B)))
    (α : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B) :
    ∃ (C : CochainComplex X.Modules ℤ) (i : A ⟶ C)
      (γ : (DerivedCategory.Q (C := X.Modules)).obj C ⟶ (DerivedCategory.Q (C := X.Modules)).obj B),
      locallyPerfect X C ∧ IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj C)) ∧
      (DerivedCategory.Q (C := X.Modules)).map i ≫ γ = α := by
  obtain ⟨M, q, hM, hq, hqα⟩ :=
    exists_perfect_denominator_across_spec_of_qc_target R j k hcover hA n hBqc hzB α
  obtain ⟨γ, hγ⟩ := CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂ _
    (DerivedCategory.mappingCone_triangle_distinguished q) α hqα
  refine ⟨CochainComplex.mappingCone q, CochainComplex.mappingCone.inr q, γ,
    locallyPerfect_mappingCone hM hA q, ?_, hγ.symm⟩
  exact (CategoryTheory.Pretriangulated.Triangle.isZero₃_of_isIso₁ _
    (DerivedCategory.mappingCone_triangle_distinguished ((restrict j).map q)) (by
      change IsIso ((DerivedCategory.Q (C := U.Modules)).map ((restrict j).map q))
      infer_instance)).of_iso
      ((DerivedCategory.Q (C := U.Modules)).mapIso
        (CochainComplex.mappingCone.mapHomologicalComplexIso q
        (Scheme.Modules.restrictFunctor j)))

end Quillen.PerfectComplexes
