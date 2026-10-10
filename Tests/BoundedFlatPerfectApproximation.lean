/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.KComparison

/-! Consumers of actual relative replacements and the original all-degree K-comparison. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.CochainComplex Quillen.SchemeSheaf Quillen.PerfectComplexes
namespace Quillen.Tests.BoundedFlatPerfectApproximation

/-- An arbitrary original map from a bounded-flat perfect complex admits the
literal admissible-cofibration/quasi-isomorphism factorization. -/
theorem original_relative_lift (X : Scheme.{u}) [CompactSpace X]
    (K : BoundedFlatPerfect X) (L : Perfect X)
    (f : (boundedFlatPerfectInclusion X).obj K ⟶ L) :
    ∃ (M : BoundedFlatPerfect X) (i : K ⟶ M)
      (p : (boundedFlatPerfectInclusion X).obj M ⟶ L),
      (boundedFlatPerfectWaldhausen X).cof i ∧ (perfectWaldhausen X).weq p ∧
      (boundedFlatPerfectInclusion X).map i ≫ p = f :=
  (boundedFlatPerfectInclusion_approximation X).lift f

/-- Genuine projective quotient terms, with no projectivity assumption on the source. -/
theorem original_relative_projective_quotient (C : Type u) [Category.{v} C] [Abelian C]
    [EnoughProjectives C] {K L : CochainComplex C ℤ} (f : K ⟶ L) (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b] :
    ∃ (M : CochainComplex C ℤ) (i : K ⟶ M) (p : M ⟶ L),
      QuasiIso p ∧ i ≫ p = f ∧ M.IsStrictlyLE (b+1) ∧
      ∀ n, Projective ((cokernel i).X n) := by
  obtain ⟨M, i, p, hM, hp, hfac, hi⟩ :=
    exists_boundedAbove_relative_projective_factorization f b
  exact ⟨M, i, p, hp, hfac, hM, relative_factorization_projective_cokernel i hi⟩

/-- Relative replacement's original short exact sequence survives arbitrary
geometric pullback, using its actual flat quotient rather than ambient exactness. -/
theorem relative_shortExact_survives_pullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    {K L : Complex Y} (f : K ⟶ L) (b : ℤ) [K.IsStrictlyLE b] [L.IsStrictlyLE b]
    (hK : ∀ n, stalkwiseFlat Y (K.X n)) :
    ∃ (M Q : Complex Y) (i : K ⟶ M) (p : M ⟶ L) (q : M ⟶ Q) (w : i ≫ q = 0),
      QuasiIso p ∧ i ≫ p = f ∧ ((ShortComplex.mk i q w).map (pullbackComplex g)).ShortExact := by
  obtain ⟨M, Q, i, p, q, w, hp, hfac, hS, _, _, _, hQ⟩ :=
    exists_boundedAbove_relative_flat_factorization Y f b hK
  refine ⟨M, Q, i, p, q, w, hp, hfac, ?_⟩
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
  intro n
  exact shortExact_pullback_of_stalkwiseFlat_quotient g
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hS n) (hQ n)

/-- Every original K-zero class has an actual bounded-flat preimage whose
image under the unchanged canonical inclusion is that original class. -/
theorem original_Kzero_preimage (X : Scheme.{u}) [CompactSpace X] (x : PerfectK X 0) :
    ∃ y : BoundedFlatPerfectK X 0, boundedFlatPerfectToPerfectKMap X 0 y = x :=
  ⟨(boundedFlatPerfectKEquiv X 0).symm x, (boundedFlatPerfectKEquiv X 0).apply_symm_apply x⟩

/-- The original canonical inclusion detects equality in every connective K-degree. -/
theorem original_Kmap_injective (X : Scheme.{u}) [CompactSpace X] (n : ℕ)
    {x y : BoundedFlatPerfectK X n}
    (h : boundedFlatPerfectToPerfectKMap X n x = boundedFlatPerfectToPerfectKMap X n y) : x = y :=
  (boundedFlatPerfectToPerfectKMap_bijective X n).1 h

/-- The computed equivalence retains the pre-existing strict-to-original-perfect map. -/
theorem original_strict_comparison (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    (boundedFlatPerfectKEquiv X n).toMonoidHom.comp (strictToBoundedFlatPerfectKMap X n) =
      strictToPerfectKMap X n := by
  simp only [MulEquiv.toMonoidHom_eq_coe]
  rw [boundedFlatPerfectKEquiv_coe]
  exact boundedFlatPerfectToPerfect_comp_strict X n

end Quillen.Tests.BoundedFlatPerfectApproximation
