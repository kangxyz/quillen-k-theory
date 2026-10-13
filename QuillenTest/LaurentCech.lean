/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Algebra.Module.FiniteCoefficientRetract
public import Quillen.Algebra.Polynomial.LaurentCech
public import Mathlib.Data.ZMod.Basic

/-! Semantic consumers of the original Laurent Čech maps and genuine finite-window
kernel retractions. The tests include non-domains, the zero ring, arbitrary
additive images, and the actual coefficient and inverse formulas. -/
@[expose] public section


noncomputable section
open CategoryTheory Polynomial LaurentPolynomial
open scoped LaurentPolynomial
open Quillen.PolynomialLaurentCech
universe u v w
namespace QuillenTest.LaurentCech

open Quillen

lemma original_zero_kernel (R : Type u) [CommRing R] (x : R[X] × R[X]) :
    difference R 0 x = 0 ↔ ∃! r : R, (Polynomial.C r, Polynomial.C r) = x := by
  constructor
  · intro hx
    refine ⟨constantRetraction R x, (difference_zero_kernel R x hx).symm, ?_⟩
    intro r hr
    have h := congrArg (constantRetraction R) hr
    simpa using h
  · rintro ⟨r, hr, _⟩
    rw [← hr]
    simp

lemma original_minus_one_inverse (R : Type u) [CommRing R]
    (a b : R[X]) (c : R[T;T⁻¹]) :
    (differenceNegOneEquiv R).symm (toLaurent a - T (-1) * invert (toLaurent b)) =
        (a,b) ∧
      difference R (-1) ((differenceNegOneEquiv R).symm c) = c :=
  ⟨(differenceNegOneEquiv R).symm_apply_apply (a,b),
    (differenceNegOneEquiv R).apply_symm_apply c⟩

lemma original_minus_two_cokernel (R : Type u) [CommRing R] (c : R[T;T⁻¹]) :
    c ∈ LinearMap.range (difference R (-2)) ↔ c.coeff (-1) = 0 := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    rw [← residue_eq_coeff]
    exact LinearMap.congr_fun (residue_difference_minusTwo R) x
  · intro h
    refine ⟨minusTwoRetraction R c, ?_⟩
    have hc := LinearMap.congr_fun (minusTwo_contraction R) c
    change difference R (-2) (minusTwoRetraction R c) +
      residueSection R (residue R c) = c at hc
    simpa only [residue_eq_coeff, h, map_zero, add_zero] using hc

lemma original_minus_two_section (R : Type u) [CommRing R] (r : R) :
    residueSection R r = LaurentPolynomial.C r * T (-1) ∧
      (residueSection R r).coeff (-1) = r := by
  refine ⟨rfl, ?_⟩
  rw [← residue_eq_coeff]
  exact LinearMap.congr_fun (residue_residueSection R) r

lemma arbitrary_additive_images (R : Type u) [CommRing R]
    {C : Type v} [Category.{w} C] [Abelian C]
    (F : ModuleCat.{u} R ⥤ C) [F.Additive] :
    ((F.mapShortComplex).obj (zeroAugmented R)).ShortExact ∧
      ((F.mapShortComplex).obj (minusTwoAugmented R)).ShortExact :=
  ⟨((zeroAugmentedSplitting R).map F).shortExact,
    ((minusTwoAugmentedSplitting R).map F).shortExact⟩

lemma finite_window_original_retraction {R : Type u} [Semiring R]
    {ι : Type v} {M : Type w} [AddCommMonoid M] [Module R M]
    (i : M →ₗ[R] (ι →₀ R)) (r : (ι →₀ R) →ₗ[R] M)
    (h : r.comp i = LinearMap.id) (s : Finset ι)
    (hi : ∀ m, (i m).support ⊆ s) :
    (∀ m, Quillen.Module.coefficientWindowRetraction r s
      (Quillen.Module.coefficientWindowInclusion i s hi m) = m) ∧
      Module.Finite R M ∧ Module.Projective R M := by
  exact ⟨fun m => LinearMap.congr_fun
    (Quillen.Module.coefficientWindowRetraction_comp_inclusion i r h s hi) m,
    Quillen.Module.finite_projective_of_coefficient_retract i r h s hi⟩

lemma original_projective_kernel {R : Type u} [Ring R] {ι : Type v}
    {A B : Type w} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Projective R B] (f : A →ₗ[R] B) (hf : Function.Surjective f)
    (i : A →ₗ[R] (ι →₀ R)) (r : (ι →₀ R) →ₗ[R] A)
    (h : r.comp i = LinearMap.id) (s : Finset ι)
    (hi : ∀ x : LinearMap.ker f, (i x.val).support ⊆ s) :
    (∃ rK : (ι →₀ R) →ₗ[R] LinearMap.ker f,
      ∀ x : LinearMap.ker f, rK (i x.val) = x) ∧
      Module.Finite R (LinearMap.ker f) ∧ Module.Projective R (LinearMap.ker f) := by
  obtain ⟨rK, hrK⟩ := Quillen.Module.exists_kernel_coefficient_retraction f hf i r h
  exact ⟨⟨rK, fun x => LinearMap.congr_fun hrK x⟩,
    Quillen.Module.finite_projective_kernel_of_coefficient_bound f hf i r h s hi⟩

lemma zero_divisor_residue :
    residue (ZMod 6) (LaurentPolynomial.C 3 * T (-1)) = 3 :=
  LinearMap.congr_fun (residue_residueSection (ZMod 6)) 3

lemma empty_ring_original_inverse (c : (ZMod 1)[T;T⁻¹]) :
    difference (ZMod 1) (-1) ((differenceNegOneEquiv (ZMod 1)).symm c) = c :=
  (differenceNegOneEquiv (ZMod 1)).apply_symm_apply c

end QuillenTest.LaurentCech
