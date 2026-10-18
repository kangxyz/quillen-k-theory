/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.MilnorK2.Basic
public import Mathlib.Tactic.Ring

/-!
# Symbol identities and additive lifts for Milnor K₂

Sign relations, skew symmetry, powers, and lifts of symbol functions are
proved in the existing integer tensor quotient. The symbol-function interface
introduces no second presentation.

Migrated from `R5Lab/KTheory/MilnorK2/Symbols.lean` at R5 commit
`d79a2e5af436f59fdfebdd8770cd27c20f850e27`, source SHA-256
`cbce55a1358e59c4a0ef965dd90603023069b5674692ce98017096d7c22b408c`.
The tensor, Steinberg span, quotient, symbol, and field-map definitions retain
their original meaning. The marked Matsumoto comparison remains separate.
-/
@[expose] public section

namespace Quillen.MilnorK2

variable (K : Type*) [Field K]

variable {K}

variable {A : Type*} [AddCommGroup A]

variable {L : Type*} [Field L]

variable {M : Type*} [Field M]

/-- The unit `1-a`, whose nonzero condition is proved from `a≠1`. -/
noncomputable def oneSub (a : Kˣ) (ha : a ≠ 1) : Kˣ :=
  Units.mk0 (1 - (a : K)) (by
    intro hz
    apply ha
    apply Units.ext
    exact (sub_eq_zero.mp hz).symm)

/-- The auxiliary `oneSub` unit has the expected field value. -/
@[simp] theorem oneSub_coe (a : Kˣ) (ha : a ≠ 1) :
    (oneSub a ha : K) = 1 - (a : K) := rfl

/-- The customary `{a,1-a}=0` form of Steinberg for nonzero field entries. -/
theorem symbol_oneSub (a : Kˣ) (ha : a ≠ 1) : symbol a (oneSub a ha) = 0 := by
  apply steinberg
  simp only [oneSub_coe]
  ring

/-- `{a,-a}=0`, derived solely from bilinearity and Steinberg. -/
theorem symbol_self_neg (a : Kˣ) : symbol a (-a) = 0 := by
  by_cases ha : a = 1
  · subst a
    exact symbol_one_left _
  have hai : a⁻¹ ≠ 1 := by simpa using ha
  have hleft := symbol_oneSub a ha
  have hright : symbol a (oneSub a⁻¹ hai) = 0 := by
    have h := symbol_oneSub a⁻¹ hai
    rw [symbol_inv_left] at h
    exact neg_eq_zero.mp h
  have heq : oneSub a ha = (-a) * oneSub a⁻¹ hai := by
    apply Units.ext
    simp only [oneSub_coe, Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val]
    rw [mul_sub, mul_one, neg_mul, mul_inv_cancel₀ a.ne_zero]
    ring
  rw [heq, symbol_mul_right, hright, add_zero] at hleft
  exact hleft

/-- `{a,a}={a,-1}`, derived from the preceding sign relation and two-torsion. -/
theorem symbol_self (a : Kˣ) : symbol a a = symbol a (-1) := by
  have h := symbol_self_neg a
  rw [show -a = a * (-1) by simp, symbol_mul_right] at h
  have hsign : symbol a (-1) + symbol a (-1) = 0 := by
    rw [← symbol_mul_right]
    simp
  exact (eq_neg_of_add_eq_zero_left h).trans (eq_neg_of_add_eq_zero_left hsign).symm

/-- Skew symmetry is proved from the Steinberg presentation rather than imposed on it. -/
theorem symbol_skew (a b : Kˣ) : symbol a b = -symbol b a := by
  have hab := symbol_self_neg (a * b)
  have ha := symbol_self_neg a
  have hb := symbol_self_neg b
  rw [show -(a * b) = (-a) * b by simp, symbol_mul_left,
    symbol_mul_right, symbol_mul_right, ha, zero_add] at hab
  rw [show -a = a * (-1) by simp, symbol_mul_right] at hab
  rw [show -b = b * (-1) by simp, symbol_mul_right] at hb
  have hcross : symbol a b + symbol b a = 0 := by
    calc
      symbol a b + symbol b a =
        (symbol a b + ((symbol b a + symbol b (-1)) + symbol b b)) -
          (symbol b b + symbol b (-1)) := by abel
      _ = 0 := by rw [hab, hb, sub_self]
  exact eq_neg_of_add_eq_zero_left hcross

/-!
## Symbol-function convenience interface

The declarations below retain the tensor quotient and its universal property.
The original R5 convenience interface was adapted from
`WeightTwoBockstein/MilnorK2.lean`, delivered revision `39cf3ab`, SHA-256
`78230009a78cdf0d706340a67b8d6a149d1d230b0e424c1476251aeb17136133`.
-/

variable {A : Type*} [AddCommGroup A]

/-- A two-entry function satisfying the bilinearity and Steinberg relations. -/
structure SymbolMap where
  /-- The value of the symbol function on two units. -/
  toFun : Kˣ → Kˣ → A
  mul_left : ∀ a b c, toFun (a * b) c = toFun a c + toFun b c
  mul_right : ∀ a b c, toFun a (b * c) = toFun a b + toFun a c
  steinberg : ∀ (a b : Kˣ), (a : K) + (b : K) = 1 → toFun a b = 0

/-- Convert a symbol function to the integer-bilinear input for the tensor lift. -/
def symbolMapBilinear (s : SymbolMap (K := K) (A := A)) :
    UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] A :=
  ({
    toFun := fun a => ({
      toFun := fun b => s.toFun a.toMul b.toMul
      map_zero' := by
        change s.toFun a.toMul 1 = 0
        have h := s.mul_right a.toMul 1 1
        exact (add_left_cancel (show s.toFun a.toMul 1 + 0 =
          s.toFun a.toMul 1 + s.toFun a.toMul 1 by
            simpa only [one_mul, add_zero] using h)).symm
      map_add' := fun b c => s.mul_right a.toMul b.toMul c.toMul
    } : UnitsAdd K →+ A).toIntLinearMap
    map_zero' := by
      apply LinearMap.ext
      intro b
      change s.toFun 1 b.toMul = 0
      have h := s.mul_left 1 1 b.toMul
      exact (add_left_cancel (show s.toFun 1 b.toMul + 0 =
        s.toFun 1 b.toMul + s.toFun 1 b.toMul by
          simpa only [one_mul, add_zero] using h)).symm
    map_add' := by
      intro a c
      apply LinearMap.ext
      intro b
      exact s.mul_left a.toMul c.toMul b.toMul
  } : UnitsAdd K →+ (UnitsAdd K →ₗ[ℤ] A)).toIntLinearMap

/-- Extend a symbol function through the existing tensor quotient as an additive map. -/
def liftSymbols (s : SymbolMap (K := K) (A := A)) : K2 K →+ A :=
  (lift (symbolMapBilinear s) (by
    intro a b hab
    exact s.steinberg a b hab)).toAddMonoidHom

/-- The additive tensor lift takes the prescribed values on symbols. -/
@[simp] theorem liftSymbols_symbol (s : SymbolMap (K := K) (A := A)) (a b : Kˣ) :
    liftSymbols s (symbol a b) = s.toFun a b := rfl

/-- Additive maps out of the tensor quotient are determined by their symbol values. -/
@[ext] theorem symbolHom_ext {f g : K2 K →+ A}
    (h : ∀ a b : Kˣ, f (symbol a b) = g (symbol a b)) : f = g :=
  addHom_ext f g h

/-- Uniqueness of the additive map extending a symbol function. -/
theorem liftSymbols_unique (s : SymbolMap (K := K) (A := A)) (f : K2 K →+ A)
    (h : ∀ a b : Kˣ, f (symbol a b) = s.toFun a b) : f = liftSymbols s := by
  apply symbolHom_ext
  intro a b
  rw [h, liftSymbols_symbol]

/-- Natural powers in the first entry act by repeated addition. -/
theorem symbol_pow_left (a b : Kˣ) (n : ℕ) :
    symbol (a ^ n) b = n • symbol a b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, symbol_mul_left, ih, succ_nsmul]

/-- Natural powers in the second entry act by repeated addition. -/
theorem symbol_pow_right (a b : Kˣ) (n : ℕ) :
    symbol a (b ^ n) = n • symbol a b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, symbol_mul_right, ih, succ_nsmul]

/-- A root of unity in the first entry gives a torsion symbol. -/
theorem nsmul_symbol_eq_zero_of_pow_eq_one (a b : Kˣ) (n : ℕ) (h : a ^ n = 1) :
    n • symbol a b = 0 := by
  rw [← symbol_pow_left, h, symbol_one_left]

/-- A root of unity in the second entry gives a torsion symbol. -/
theorem nsmul_symbol_eq_zero_of_pow_eq_one_right (a b : Kˣ) (n : ℕ) (h : b ^ n = 1) :
    n • symbol a b = 0 := by
  rw [← symbol_pow_right, h, symbol_one_right]

end Quillen.MilnorK2
