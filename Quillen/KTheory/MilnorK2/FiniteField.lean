/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.MilnorK2.Symbols
public import Mathlib.RingTheory.IntegralDomain

/-!
# Integral Milnor K₂ of every finite field

Every symbol in the existing tensor quotient vanishes over a finite field,
so the integral Milnor group is a subsingleton. The proof uses cyclicity of
the finite unit group, skew symmetry, and a finite-fibre Steinberg argument.
It includes characteristic two and the fields with two and three elements.
No comparison with Quillen K₂ or finite-coefficient vanishing is asserted.

Migrated from `R5Lab/KTheory/MilnorK2/FiniteField.lean` at R5 commit
`d79a2e5af436f59fdfebdd8770cd27c20f850e27`, source SHA-256
`82ed4eded5a595428db8f40561d75f8ffd6479aa0bd0c87fe65f781f93a77db5`.
The tensor, Steinberg span, quotient, symbol, and field-map definitions retain
their original meaning. The marked Matsumoto comparison remains separate.
Finite unit-group cyclicity is supplied by the pinned Mathlib instance in
`Mathlib/RingTheory/IntegralDomain.lean`, lines 130–145.
-/
@[expose] public section

noncomputable section

namespace Quillen.MilnorK2

variable {k : Type*} [Field k] [Finite k]

/-- A generating unit has zero diagonal symbol, by a finite-fibre Steinberg argument. -/
private theorem finite_generator_symbol_self_eq_zero (t : kˣ)
    (ht : ∀ a : kˣ, ∃ n : ℕ, t ^ n = a) : symbol t t = 0 := by
  classical
  by_contra hs
  have htwo : symbol t t + symbol t t = 0 :=
    add_eq_zero_iff_eq_neg.mpr (symbol_skew t t)
  have hm (n : ℕ) : n • symbol t t = 0 ∨ n • symbol t t = symbol t t := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul]
      rcases ih with h | h
      · right; simp [h]
      · left; rw [h, htwo]
  have hvalues (a : kˣ) : symbol t a = 0 ∨ symbol t a = symbol t t := by
    obtain ⟨n, rfl⟩ := ht a
    rw [symbol_pow_right]
    exact hm n
  let N := {a : kˣ // symbol t a ≠ 0}
  have hne (a : N) : a.val ≠ 1 := by
    intro h
    apply a.property
    rw [h, symbol_one_right]
  have hcomplement (a : N) : symbol t (oneSub a.val (hne a)) = 0 := by
    rcases hvalues (oneSub a.val (hne a)) with h | h
    · exact h
    · obtain ⟨n, hn⟩ := ht a.val
      have he : symbol a.val (oneSub a.val (hne a)) = symbol t a.val := by
        nth_rw 1 [← hn]
        rw [symbol_pow_left, h, ← symbol_pow_right, hn]
      exact (a.property (he.symm.trans (symbol_oneSub a.val (hne a)))).elim
  let f : N → N := fun a => ⟨t * oneSub a.val (hne a), by
    rw [symbol_mul_right, hcomplement, add_zero]
    exact hs⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    have he : t * oneSub a.val (hne a) = t * oneSub b.val (hne b) :=
      congrArg Subtype.val hab
    have he' := congrArg Units.val (mul_left_cancel he)
    simp only [oneSub_coe] at he'
    simpa using congrArg (fun x : k => 1 - x) he'
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective hfinj) (⟨t, hs⟩ : N)
  have he : t * oneSub a.val (hne a) = t := congrArg Subtype.val ha
  have he' : oneSub a.val (hne a) = 1 := by
    apply mul_left_cancel (a := t)
    simpa using he
  have hz : (a.val : k) = 0 := by
    have hh := congrArg Units.val he'
    simpa only [oneSub_coe, Units.val_one, sub_eq_self] using hh
  exact a.val.ne_zero hz

/-- Every integral Milnor symbol over a finite field is zero. -/
theorem symbol_eq_zero_of_finite (a b : kˣ) : symbol a b = 0 := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := kˣ)
  have hp (c : kˣ) : ∃ n : ℕ, t ^ n = c := by
    exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (ht c))
  have hs := finite_generator_symbol_self_eq_zero t hp
  obtain ⟨m, rfl⟩ := hp a
  obtain ⟨n, rfl⟩ := hp b
  rw [symbol_pow_left, symbol_pow_right, hs, smul_zero, smul_zero]

/-- Symbols generate the actual tensor quotient, so every Milnor class is zero. -/
theorem k2_eq_zero_of_finite (z : K2 k) : z = 0 := by
  have he : (LinearMap.id : K2 k →ₗ[ℤ] K2 k) = 0 := by
    apply linearMap_ext
    intro a b
    simpa using symbol_eq_zero_of_finite a b
  exact congrArg (fun f : K2 k →ₗ[ℤ] K2 k => f z) he

/-- The actual integral Milnor group of any finite field has one element. -/
instance finiteField_k2_subsingleton : Subsingleton (K2 k) :=
  ⟨fun a b => (k2_eq_zero_of_finite a).trans (k2_eq_zero_of_finite b).symm⟩

end Quillen.MilnorK2
