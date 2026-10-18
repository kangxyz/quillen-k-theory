/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Milnor K₂ as an integer tensor quotient

`K2 K` is the quotient of `Additive Kˣ ⊗[ℤ] Additive Kˣ` by the integer
span of the Steinberg tensors. Symbols, bilinearity, Steinberg relations,
and the universal property are constructed from this actual quotient.
There is no identification with Quillen K₂ in this module.

Migrated from `R5Lab/KTheory/MilnorK2/Basic.lean` at R5 commit
`d79a2e5af436f59fdfebdd8770cd27c20f850e27`, source SHA-256
`592f8b07a4d5cf606df0245d92d0e19dceabf1ba22cff229233897210bffe2ed`.
The tensor, Steinberg span, quotient, symbol, and field-map definitions retain
their original meaning. The marked Matsumoto comparison remains separate.
`UnitsAdd` absorbs the original Milnor-specific units wrapper, SHA-256
`12795db7b1c7cdfca0d5c29fbc20230bdb76e94b89da09a2b3b588ca2159a9be`.
-/
@[expose] public section

namespace Quillen.MilnorK2

variable (K : Type*) [Field K]

/-- The multiplicative units, written additively for the integer tensor product. -/
abbrev UnitsAdd := Additive Kˣ

/-- The tensor presentation before imposing the auxiliary Steinberg relations. -/
abbrev UnitTensor := TensorProduct ℤ (UnitsAdd K) (UnitsAdd K)

/-- Steinberg tensors for nonzero `a,b` with `a+b=1`; auxiliary symbol foundations. -/
def steinbergGenerators : Set (UnitTensor K) :=
  {t | ∃ a b : Kˣ, (a : K) + (b : K) = 1 ∧
    t = TensorProduct.tmul ℤ (Additive.ofMul a) (Additive.ofMul b)}

/-- The integer span of the Steinberg tensors, with no additional relations imposed. -/
def steinbergSpan : Submodule ℤ (UnitTensor K) :=
  Submodule.span ℤ (steinbergGenerators K)

/-- Milnor K₂ as the actual integer tensor quotient; source scope is documented above. -/
abbrev K2 := UnitTensor K ⧸ steinbergSpan K

variable {K}

/-- The symbol `{a,b}` in the constructed Milnor group, used by K2-018. -/
def symbol (a b : Kˣ) : K2 K :=
  (steinbergSpan K).mkQ (TensorProduct.tmul ℤ (Additive.ofMul a) (Additive.ofMul b))

variable (K)

/-- The genuine integer-bilinear symbol map arising from the tensor quotient. -/
def symbolBilinear : UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] K2 K :=
  (TensorProduct.mk ℤ (UnitsAdd K) (UnitsAdd K)).compr₂ (steinbergSpan K).mkQ

variable {K}

/-- The bilinear map evaluates to the constructed symbol. -/
@[simp] theorem symbolBilinear_apply (a b : Kˣ) :
    symbolBilinear K (Additive.ofMul a) (Additive.ofMul b) = symbol a b := rfl

/-- Multiplicative bilinearity in the first field argument. -/
theorem symbol_mul_left (a b c : Kˣ) :
    symbol (a * b) c = symbol a c + symbol b c := by
  change (steinbergSpan K).mkQ
    (TensorProduct.tmul ℤ (Additive.ofMul a + Additive.ofMul b) (Additive.ofMul c)) = _
  rw [TensorProduct.add_tmul, map_add]
  rfl

/-- Multiplicative bilinearity in the second field argument. -/
theorem symbol_mul_right (a b c : Kˣ) :
    symbol a (b * c) = symbol a b + symbol a c := by
  change (steinbergSpan K).mkQ
    (TensorProduct.tmul ℤ (Additive.ofMul a) (Additive.ofMul b + Additive.ofMul c)) = _
  rw [TensorProduct.tmul_add, map_add]
  rfl

/-- A symbol with first entry one vanishes; auxiliary symbol algebra. -/
@[simp] theorem symbol_one_left (a : Kˣ) : symbol 1 a = 0 := by
  simp [symbol]

/-- A symbol with second entry one vanishes; auxiliary symbol algebra. -/
@[simp] theorem symbol_one_right (a : Kˣ) : symbol a 1 = 0 := by
  simp [symbol]

/-- Inverting the first entry negates the symbol. -/
@[simp] theorem symbol_inv_left (a b : Kˣ) : symbol a⁻¹ b = -symbol a b := by
  simp [symbol, ofMul_inv, TensorProduct.neg_tmul]

/-- Inverting the second entry negates the symbol. -/
@[simp] theorem symbol_inv_right (a b : Kˣ) : symbol a b⁻¹ = -symbol a b := by
  simp [symbol, ofMul_inv, TensorProduct.tmul_neg]

/-- Division expands as subtraction in the first entry. -/
theorem symbol_div_left (a b c : Kˣ) : symbol (a / b) c = symbol a c - symbol b c := by
  rw [div_eq_mul_inv, symbol_mul_left, symbol_inv_left, sub_eq_add_neg]

/-- Division expands as subtraction in the second entry. -/
theorem symbol_div_right (a b c : Kˣ) : symbol a (b / c) = symbol a b - symbol a c := by
  rw [div_eq_mul_inv, symbol_mul_right, symbol_inv_right, sub_eq_add_neg]

/-- The Steinberg relation is proved in the actual quotient, not supplied as an axiom. -/
theorem steinberg (a b : Kˣ) (h : (a : K) + (b : K) = 1) : symbol a b = 0 := by
  change (Submodule.Quotient.mk
    (TensorProduct.tmul ℤ (Additive.ofMul a) (Additive.ofMul b)) : K2 K) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨a, b, h, rfl⟩

variable {A : Type*} [AddCommGroup A]

/-- A bilinear map killing Steinberg tensors descends to the constructed Milnor quotient. -/
def lift (b : UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] A)
    (hb : ∀ a c : Kˣ, (a : K) + (c : K) = 1 →
      b (Additive.ofMul a) (Additive.ofMul c) = 0) : K2 K →ₗ[ℤ] A :=
  (steinbergSpan K).liftQ (TensorProduct.lift b) (by
    rw [steinbergSpan, Submodule.span_le]
    rintro t ⟨a, c, hac, rfl⟩
    exact hb a c hac)

/-- The descended map has its prescribed symbol values. -/
@[simp] theorem lift_symbol (b : UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] A)
    (hb : ∀ a c : Kˣ, (a : K) + (c : K) = 1 →
      b (Additive.ofMul a) (Additive.ofMul c) = 0) (a c : Kˣ) :
    lift b hb (symbol a c) = b (Additive.ofMul a) (Additive.ofMul c) := rfl

/-- Integer-linear maps out of Milnor K₂ are determined by all symbols. -/
@[ext] theorem linearMap_ext (f g : K2 K →ₗ[ℤ] A)
    (h : ∀ a b : Kˣ, f (symbol a b) = g (symbol a b)) : f = g := by
  apply Submodule.linearMap_qext
  apply TensorProduct.ext'
  intro a b
  exact h a.toMul b.toMul

/-- Additive maps out of Milnor K₂ are determined by all symbols. -/
@[ext] theorem addHom_ext (f g : K2 K →+ A)
    (h : ∀ a b : Kˣ, f (symbol a b) = g (symbol a b)) : f = g := by
  apply AddMonoidHom.toIntLinearMap_injective
  exact linearMap_ext f.toIntLinearMap g.toIntLinearMap h

/-- The universal property of the actual Milnor presentation, including uniqueness. -/
theorem existsUnique_lift (b : UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] A)
    (hb : ∀ a c : Kˣ, (a : K) + (c : K) = 1 →
      b (Additive.ofMul a) (Additive.ofMul c) = 0) :
    ∃! f : K2 K →ₗ[ℤ] A, ∀ a c : Kˣ,
      f (symbol a c) = b (Additive.ofMul a) (Additive.ofMul c) := by
  refine ⟨lift b hb, fun a c => lift_symbol b hb a c, ?_⟩
  intro f hf
  exact linearMap_ext f (lift b hb) (fun a c => (hf a c).trans (lift_symbol b hb a c).symm)

end Quillen.MilnorK2
