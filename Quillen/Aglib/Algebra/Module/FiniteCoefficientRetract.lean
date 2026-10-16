/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Actual finite-coefficient retracts

A split submodule of a coefficient-free module whose original inclusion lands
in one finite coefficient window is a literal retract of that finite free
window. This supplies the finite-projectivity step for a split Čech kernel;
finite support alone would not suffice over an arbitrary ring.
-/
@[expose] public section

noncomputable section
universe u v w
namespace Quillen.Module
variable {R : Type u} [Semiring R] {ι : Type v}
  {M : Type w} [AddCommMonoid M] [Module R M]

/-- The original inclusion of a finite coefficient window into all coefficients. -/
def coefficientWindowEmbedding (s : Finset ι) : (s →₀ R) →ₗ[R] (ι →₀ R) :=
  (Finsupp.supported R R (s : Set ι)).subtype.comp
    (Finsupp.supportedEquivFinsupp (R := R) (M := R) (s : Set ι)).symm.toLinearMap

/-- Factor the specified original inclusion through its actual finite window. -/
def coefficientWindowInclusion (i : M →ₗ[R] (ι →₀ R)) (s : Finset ι)
    (hi : ∀ m, (i m).support ⊆ s) : M →ₗ[R] (s →₀ R) :=
  (Finsupp.supportedEquivFinsupp (R := R) (M := R) (s : Set ι)).toLinearMap.comp
    (i.codRestrict (Finsupp.supported R R (s : Set ι))
      (fun m => (Finsupp.mem_supported R (i m)).mpr (hi m)))

lemma coefficientWindowEmbedding_comp_inclusion (i : M →ₗ[R] (ι →₀ R))
    (s : Finset ι) (hi : ∀ m, (i m).support ⊆ s) :
    (coefficientWindowEmbedding (R := R) s).comp
      (coefficientWindowInclusion i s hi) = i := by
  ext m
  simp [coefficientWindowEmbedding, coefficientWindowInclusion]

/-- Restrict the already-genuine ambient retraction to the finite free window. -/
def coefficientWindowRetraction (r : (ι →₀ R) →ₗ[R] M) (s : Finset ι) :
    (s →₀ R) →ₗ[R] M := r.comp (coefficientWindowEmbedding s)

lemma coefficientWindowRetraction_comp_inclusion
    (i : M →ₗ[R] (ι →₀ R)) (r : (ι →₀ R) →ₗ[R] M)
    (h : r.comp i = LinearMap.id) (s : Finset ι)
    (hi : ∀ m, (i m).support ⊆ s) :
    (coefficientWindowRetraction r s).comp (coefficientWindowInclusion i s hi) =
      LinearMap.id := by
  unfold coefficientWindowRetraction
  rw [LinearMap.comp_assoc, coefficientWindowEmbedding_comp_inclusion, h]

/-- An actual split finite-window inclusion gives a finite-projective module. -/
theorem finite_projective_of_coefficient_retract
    (i : M →ₗ[R] (ι →₀ R)) (r : (ι →₀ R) →ₗ[R] M)
    (h : r.comp i = LinearMap.id) (s : Finset ι)
    (hi : ∀ m, (i m).support ⊆ s) :
    Module.Finite R M ∧ Module.Projective R M := by
  have hs := coefficientWindowRetraction_comp_inclusion i r h s hi
  refine ⟨Module.Finite.of_surjective (coefficientWindowRetraction r s) ?_,
    Module.Projective.of_split (coefficientWindowInclusion i s hi)
      (coefficientWindowRetraction r s) hs⟩
  intro m
  exact ⟨coefficientWindowInclusion i s hi m, LinearMap.congr_fun hs m⟩

end Quillen.Module

namespace Quillen.Module
section Kernel
variable {R : Type u} [Ring R] {ι : Type v}
  {A B : Type w} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- A surjection onto a projective module supplies the genuine kernel retraction
inside any specified coefficient-free retract of its source. -/
theorem exists_kernel_coefficient_retraction [Module.Projective R B]
    (f : A →ₗ[R] B) (hf : Function.Surjective f)
    (i : A →ₗ[R] (ι →₀ R)) (r : (ι →₀ R) →ₗ[R] A)
    (h : r.comp i = LinearMap.id) :
    ∃ rK : (ι →₀ R) →ₗ[R] LinearMap.ker f,
      rK.comp (i.comp (LinearMap.ker f).subtype) = LinearMap.id := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  let k : A →ₗ[R] LinearMap.ker f :=
    (LinearMap.id - s.comp f).codRestrict (LinearMap.ker f) (fun x => by
      change f (x - s (f x)) = 0
      have hx := LinearMap.congr_fun hs (f x)
      change f (s (f x)) = f x at hx
      rw [map_sub, hx, sub_self])
  refine ⟨k.comp r, ?_⟩
  ext x
  change r (i x.val) - s (f (r (i x.val))) = x.val
  have hri := LinearMap.congr_fun h x.val
  change r (i x.val) = x.val at hri
  have hx := x.property
  change f x.val = 0 at hx
  rw [hri, hx, map_zero, sub_zero]

/-- The original kernel is finite-projective once the genuine split-surjection
kernel has a uniform finite coefficient bound in its specified embedding. -/
theorem finite_projective_kernel_of_coefficient_bound [Module.Projective R B]
    (f : A →ₗ[R] B) (hf : Function.Surjective f)
    (i : A →ₗ[R] (ι →₀ R)) (r : (ι →₀ R) →ₗ[R] A)
    (h : r.comp i = LinearMap.id) (s : Finset ι)
    (hi : ∀ x : LinearMap.ker f, (i x.val).support ⊆ s) :
    Module.Finite R (LinearMap.ker f) ∧ Module.Projective R (LinearMap.ker f) := by
  obtain ⟨rK, hrK⟩ := exists_kernel_coefficient_retraction f hf i r h
  exact finite_projective_of_coefficient_retract (i.comp (LinearMap.ker f).subtype)
    rK hrK s hi

end Kernel
end Quillen.Module
