/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenGluing.OneChartDenominator
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom

/-!
# One-chart denominator regression statements

Records chain nullhomotopies and supported perfect factorizations for a cover by
a compact open and an affine chart, with lower-bounded quasicoherent-homology
targets. The final statement expresses injectivity of restriction to the other
chart when the target is derived-zero on the first open.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace QuillenTest.OneChartDenominator
attribute [local instance] Affine.standardDerivedSheaves

/-- An actual original chain map is annihilated by a genuine chain homotopy
after an actual perfect denominator, still weak on the same open. -/
theorem original_chain_nullhomotopy (R : CommRingCat.{u})
    {U X : Scheme.{u}} [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {A B : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) (n : ℤ) [B.IsGE n]
    (hB : ∀ m, (B.homology m).IsQuasicoherent)
    (hzB : IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B))) (f : A ⟶ B) :
    ∃ (P : CochainComplex X.Modules ℤ) (q : P ⟶ A), locallyPerfect X P ∧
      QuasiIso ((restrict j).map q) ∧ Nonempty (Homotopy (q ≫ f) 0) := by
  obtain ⟨P, q, hP, hq, hqf⟩ :=
    exists_perfect_denominator_across_spec_of_qc_target R j k hcover hA n hB hzB
      ((DerivedCategory.Q (C := X.Modules)).map
      f)
  let : HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
  have he : DerivedCategory.Q.{u+1}.map (q ≫ f) = DerivedCategory.Q.{u+1}.map (0 : P ⟶ B) := by
    change (DerivedCategory.Q (C := X.Modules)).map (q ≫ f) =
      (DerivedCategory.Q (C := X.Modules)).map 0
    simpa only [Functor.map_comp, Functor.map_zero] using hqf
  obtain ⟨M, s, hs, ⟨H⟩⟩ :=
    Quillen.CochainComplex.exists_pre_quasiIso_homotopy_of_derived_eq (q ≫ f) 0 he
  refine ⟨M, s ≫ q, (locallyPerfect_iff_of_quasiIso s).mpr hP, ?_, ?_⟩
  · rw [(restrict j).map_comp]
    infer_instance
  · exact ⟨by simpa only [Category.assoc, comp_zero] using H⟩

/-- The first arrow in the actual supported factorization remains an original
chain map, and its restriction has zero derived image. -/
theorem original_factorization_has_supported_first_arrow (R : CommRingCat.{u})
    {U X : Scheme.{u}} [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {A B : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) (n : ℤ) [B.IsGE n]
    (hB : ∀ m, (B.homology m).IsQuasicoherent)
    (hzB : IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B)))
    (α : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B) :
    ∃ (C : CochainComplex X.Modules ℤ) (i : A ⟶ C)
      (γ : (DerivedCategory.Q (C := X.Modules)).obj C ⟶ (DerivedCategory.Q (C := X.Modules)).obj B),
      locallyPerfect X C ∧ IsZero ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj C)) ∧
      (DerivedCategory.Q (C := X.Modules)).map i ≫ γ = α ∧ (DerivedCategory.Q (C := U.Modules)).map
        ((restrict j).map i) = 0 := by
  obtain ⟨C, i, γ, hC, hzC, hγ⟩ :=
    exists_perfect_factorization_across_spec_of_qc_target R j k hcover hA n hB hzB α
  exact ⟨C, i, γ, hC, hzC, hγ, hzC.eq_of_tgt _ _⟩

/-- The zero-target condition removes precisely the genuine MV ambiguity:
restriction to the other chart is injective on these original derived maps. -/
theorem original_restriction_injective {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {A B : CochainComplex X.Modules ℤ} (hzB : IsZero
      ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj B)))
    (α β : (DerivedCategory.Q (C := X.Modules)).obj A ⟶ (DerivedCategory.Q (C := X.Modules)).obj B)
    (h : restrictDerivedHom k α = restrictDerivedHom k β) : α = β := by
  apply sub_eq_zero.mp
  apply derivedHom_eq_zero_of_target_zero_and_cover j k hcover hzB
  simp only [restrictDerivedHom, Functor.map_sub, Preadditive.comp_sub, Preadditive.sub_comp] at h ⊢
  exact sub_eq_zero.mpr h

end QuillenTest.OneChartDenominator
