/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# A positive-dimensional local ring with principal maximal ideal is a domain

The proof uses Krull's intersection theorem to write each nonzero element as
a power of a generator times a unit. Positive dimension rules out a nilpotent
generator. This supplies the missing domain step in dimension-one regularity.
-/
@[expose] public section

noncomputable section
universe u
open IsLocalRing

namespace Quillen.RegularLocal
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Krull intersection gives a last power of the maximal ideal containing a
specified nonzero element. -/
theorem exists_mem_pow_not_mem_succ (a : R) (ha : a ≠ 0) :
    ∃ n : ℕ, a ∈ (maximalIdeal R) ^ n ∧ a ∉ (maximalIdeal R) ^ (n + 1) := by
  classical
  by_contra! h
  have hmem (n : ℕ) : a ∈ (maximalIdeal R) ^ n := by
    induction n with
    | zero => simp
    | succ n ih => exact h n ih
  have hall : a ∈ ⨅ n : ℕ, (maximalIdeal R) ^ n := (Submodule.mem_iInf _).mpr hmem
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top] at hall
  exact ha hall

/-- In a noetherian local ring whose maximal ideal is `(π)`, every nonzero
element is a power of `π` times a unit. No domain assumption is used. -/
theorem exists_pow_mul_unit (π a : R) (hπ : maximalIdeal R = Ideal.span {π})
    (ha : a ≠ 0) : ∃ (n : ℕ) (b : R), IsUnit b ∧ a = π ^ n * b := by
  obtain ⟨n, hn, hn'⟩ := exists_mem_pow_not_mem_succ R a ha
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hn
  obtain ⟨b, hb⟩ := hn
  refine ⟨n, b, ?_, hb⟩
  by_contra hunit
  have hbmem : b ∈ maximalIdeal R := hunit
  rw [hπ, Ideal.mem_span_singleton] at hbmem
  obtain ⟨c, hc⟩ := hbmem
  apply hn'
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨c, by rw [hb, hc, pow_succ, mul_assoc]⟩

omit [IsNoetherianRing R] in
/-- A nilpotent generator of the maximal ideal forces dimension zero. -/
theorem dimension_zero_of_nilpotent_generator (π : R)
    (hπ : maximalIdeal R = Ideal.span {π}) (hnil : IsNilpotent π) :
    ringKrullDim R = 0 := by
  have : Ring.KrullDimLE 0 R := Ring.KrullDimLE.mk₀ (fun I hI => by
    have hle : maximalIdeal R ≤ I := by
      rw [hπ, Ideal.span_le, Set.singleton_subset_iff]
      obtain ⟨n, hn⟩ := hnil
      exact hI.mem_of_pow_mem n (hn ▸ I.zero_mem)
    have he := (maximalIdeal.isMaximal R).eq_of_le hI.ne_top hle
    exact he ▸ maximalIdeal.isMaximal R)
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

/-- Positive dimension and a principal maximal ideal imply that the local
noetherian ring is a domain. This uses an actual element factorization and
Krull intersection, not an assumed regularity theorem. -/
theorem isDomain_of_principal_maximalIdeal
    (h : (maximalIdeal R).IsPrincipal) (hd : ringKrullDim R ≠ 0) : IsDomain R := by
  obtain ⟨π, hπ⟩ := h
  have hnil : ¬IsNilpotent π := fun hp => hd (dimension_zero_of_nilpotent_generator R π hπ hp)
  have : NoZeroDivisors R := ⟨by
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr hb
    obtain ⟨n, x, hx, hax⟩ := exists_pow_mul_unit R π a hπ ha
    obtain ⟨m, y, hy, hby⟩ := exists_pow_mul_unit R π b hπ hb
    have hzero : π ^ (n + m) * (x * y) = 0 := by
      calc
        π ^ (n + m) * (x * y) = (π ^ n * x) * (π ^ m * y) := by rw [pow_add]; ring
        _ = 0 := by rw [← hax, ← hby]; exact hab
    exact False.elim (hnil ⟨n + m, (hx.mul hy).mul_left_eq_zero.mp hzero⟩)⟩
  exact NoZeroDivisors.to_isDomain R

end Quillen.RegularLocal
