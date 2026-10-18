/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.MilnorK2.Symbols
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Tactic.Abel

/-!
# The tame map on the actual Milnor tensor quotient

`DiscreteResidueData` records elementary valuation and reduction identities.
`rawTame` is proved bilinear and Steinberg before `tame` descends through the
existing tensor quotient `K2`. The ordered convention is `∂{u,π}=ū`, hence
`∂{π,u}=ū⁻¹`. No desired tame-symbol law is assumed in the data.

An actual DVR supplies these data in `DVR.Basic`; `DVR.TameKernel` proves the
algebraic kernel statement. These modules do not identify Quillen K₂ of the
DVR, prove its injection or generation, or provide a marked product comparison.

The definitions are migrated from the R5 sources
`Aglib/RingTheory/Valuation/ResidueData.lean`, SHA-256
`240b5fffc8d72d3c950037f4c557a2f54cac2f3716a3a8f8701fe4edd543b2d7`,
and `KTheory/MilnorK2/Residue.lean`, SHA-256
`fbcf4be4844b0dcd031c2f102b0c902da82b25b1bc4168462a6befc618e8a040`.
The actual tensor quotient and ordered symbol formulas are preserved.
-/
@[expose] public section

namespace Quillen.MilnorK2

variable {K k : Type*} [Field K] [Field k]
/-- Additive notation for the residue sign `-1` in the source's tame-symbol formula. -/
def residueSign (k : Type*) [Field k] : UnitsAdd k := Additive.ofMul (-1)

/-- The sign is killed by two, including in residue characteristic two. -/
theorem residueSign_add_self : residueSign k + residueSign k = 0 := by
  change Additive.ofMul ((-1 : kˣ) * (-1)) = 0
  simp

/-- Explicit normalized valuation/residue background; its semantic scope is detailed above. -/
structure DiscreteResidueData (K k : Type*) [Field K] [Field k] where
  /-- The normalized integer valuation on field units. -/
  value : UnitsAdd K →ₗ[ℤ] ℤ
  /-- The residue of the unit obtained after removing the uniformizer power. -/
  unitPart : UnitsAdd K →ₗ[ℤ] UnitsAdd k
  /-- The chosen normalized uniformizer as an actual field unit. -/
  uniformizer : Kˣ
  value_uniformizer : value (Additive.ofMul uniformizer) = 1
  unitPart_uniformizer : unitPart (Additive.ofMul uniformizer) = 0
  unitPart_neg_one : unitPart (Additive.ofMul (-1)) = residueSign k
  positive : ∀ a b : Kˣ, (a : K) + (b : K) = 1 → 0 < value (Additive.ofMul a) →
    value (Additive.ofMul b) = 0 ∧ unitPart (Additive.ofMul b) = 0
  negative : ∀ a b : Kˣ, (a : K) + (b : K) = 1 → value (Additive.ofMul a) < 0 →
    value (Additive.ofMul b) = value (Additive.ofMul a) ∧
      unitPart (Additive.ofMul b) = unitPart (Additive.ofMul a) + residueSign k

/-- A sign killed by two is killed by every integer `m²-m`; auxiliary residue algebra. -/
theorem square_sub_smul_eq_zero {A : Type*} [AddCommGroup A]
    (x : A) (hx : x + x = 0) (m : ℤ) : (m * m - m) • x = 0 := by
  have htwo : (2 : ℤ) • x = 0 := by simpa only [two_smul] using hx
  refine Int.induction_on m ?_ ?_ ?_
  · simp
  · intro z hz
    have heq : ((z : ℤ) + 1) * ((z : ℤ) + 1) - ((z : ℤ) + 1) =
        ((z : ℤ) * (z : ℤ) - (z : ℤ)) + (z : ℤ) * 2 := by ring
    rw [heq, add_zsmul, hz, mul_zsmul, htwo, zsmul_zero, add_zero]
  · intro z hz
    have heq : (-(z : ℤ) - 1) * (-(z : ℤ) - 1) - (-(z : ℤ) - 1) =
        (-(z : ℤ) * -(z : ℤ) - -(z : ℤ)) + (1 + (z : ℤ)) * 2 := by ring
    rw [heq, add_zsmul, hz, mul_zsmul, htwo, zsmul_zero, add_zero]

/-- Elementary DVR reduction of `a+b=1` when both entries have valuation zero. -/
def UnitReductionCompatible (d : DiscreteResidueData K k) : Prop :=
  ∀ a b : Kˣ, (a : K) + (b : K) = 1 →
    d.value (Additive.ofMul a) = 0 → d.value (Additive.ofMul b) = 0 →
    ((d.unitPart (Additive.ofMul a)).toMul : k) +
      ((d.unitPart (Additive.ofMul b)).toMul : k) = 1

variable {K k : Type*} [Field K] [Field k]

/-- The signed tame formula before proving bilinearity or descent. -/
def rawTame (d : DiscreteResidueData K k) (a b : UnitsAdd K) : UnitsAdd k :=
  (d.value a * d.value b) • residueSign k + d.value b • d.unitPart a -
    d.value a • d.unitPart b

/-- Bilinearity of the signed formula, proved from the two homomorphisms in the data. -/
def tameBilinear (d : DiscreteResidueData K k) :
    UnitsAdd K →ₗ[ℤ] UnitsAdd K →ₗ[ℤ] UnitsAdd k :=
  LinearMap.mk₂ ℤ (rawTame d)
    (by
      intro a b c
      simp only [rawTame, map_add, add_mul, add_zsmul, zsmul_add]
      abel)
    (by
      intro r a b
      simp [rawTame, map_smul, smul_add, smul_sub, smul_smul,
        mul_comm, mul_left_comm])
    (by
      intro a b c
      simp only [rawTame, map_add, mul_add, add_zsmul, zsmul_add]
      abel)
    (by
      intro r a b
      simp [rawTame, map_smul, smul_add, smul_sub, smul_smul,
        mul_comm, mul_left_comm])

/-- Steinberg is derived from elementary positive/negative valuation cases and sign parity. -/
theorem rawTame_steinberg (d : DiscreteResidueData K k) (a b : Kˣ)
    (hab : (a : K) + (b : K) = 1) : rawTame d (Additive.ofMul a) (Additive.ofMul b) = 0 := by
  rcases lt_trichotomy (d.value (Additive.ofMul a)) 0 with hneg | hzero | hpos
  · obtain ⟨hvb, hub⟩ := d.negative a b hab hneg
    calc
      rawTame d (Additive.ofMul a) (Additive.ofMul b) =
        (d.value (Additive.ofMul a) * d.value (Additive.ofMul a)) • residueSign k +
          d.value (Additive.ofMul a) • d.unitPart (Additive.ofMul a) -
          d.value (Additive.ofMul a) •
            (d.unitPart (Additive.ofMul a) + residueSign k) := by rw [rawTame, hvb, hub]
      _ = (d.value (Additive.ofMul a) * d.value (Additive.ofMul a) -
          d.value (Additive.ofMul a)) • residueSign k := by
        rw [zsmul_add, sub_zsmul]
        abel
      _ = 0 := square_sub_smul_eq_zero (residueSign k) residueSign_add_self _
  · rcases lt_trichotomy (d.value (Additive.ofMul b)) 0 with hbneg | hbzero | hbpos
    · obtain ⟨hva, _⟩ := d.negative b a (by simpa [add_comm] using hab) hbneg
      have hvb : d.value (Additive.ofMul b) = 0 := hva.symm.trans hzero
      simp [rawTame, hzero, hvb]
    · simp [rawTame, hzero, hbzero]
    · obtain ⟨_, hua⟩ := d.positive b a (by simpa [add_comm] using hab) hbpos
      simp [rawTame, hzero, hua]
  · obtain ⟨hvb, hub⟩ := d.positive a b hab hpos
    simp [rawTame, hvb, hub]

/-- The actual descended tame homomorphism, after proving bilinearity and Steinberg. -/
def tame (d : DiscreteResidueData K k) : K2 K →ₗ[ℤ] UnitsAdd k :=
  lift (tameBilinear d) (fun a b hab => rawTame_steinberg d a b hab)

/-- The descended map evaluates to the raw formula on every symbol. -/
@[simp] theorem tame_symbol (d : DiscreteResidueData K k) (a b : Kˣ) :
    tame d (symbol a b) = rawTame d (Additive.ofMul a) (Additive.ofMul b) := rfl

/-- The tame homomorphism written with multiplicative residue units as target. -/
def tameValue (d : DiscreteResidueData K k) (x : K2 K) : kˣ := (tame d x).toMul

/-- The zero Milnor class has tame value one. -/
@[simp] theorem tameValue_zero (d : DiscreteResidueData K k) : tameValue d 0 = 1 := by
  change (tame d 0).toMul = 1
  rw [map_zero]
  rfl

/-- Addition of Milnor classes becomes multiplication of residue units. -/
theorem tameValue_add (d : DiscreteResidueData K k) (x y : K2 K) :
    tameValue d (x + y) = tameValue d x * tameValue d y := by
  change (tame d (x + y)).toMul = _
  rw [map_add]
  rfl

/-- The standard sign-correct multiplicative formula in the source's normalization. -/
theorem tameValue_symbol (d : DiscreteResidueData K k) (a b : Kˣ) :
    tameValue d (symbol a b) =
      (-1 : kˣ) ^ (d.value (Additive.ofMul a) * d.value (Additive.ofMul b)) *
        (d.unitPart (Additive.ofMul a)).toMul ^ d.value (Additive.ofMul b) /
        (d.unitPart (Additive.ofMul b)).toMul ^ d.value (Additive.ofMul a) := rfl

/-- A symbol of two valuation units has zero additive tame value. -/
theorem tame_units (d : DiscreteResidueData K k) (u v : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) (hv : d.value (Additive.ofMul v) = 0) :
    tame d (symbol u v) = 0 := by simp [tame_symbol, rawTame, hu, hv]

/-- The source convention `∂{u,π}=ū`, expressed additively in residue units. -/
theorem tame_unit_uniformizer (d : DiscreteResidueData K k) (u : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) :
    tame d (symbol u d.uniformizer) = d.unitPart (Additive.ofMul u) := by
  simp [tame_symbol, rawTame, hu, d.value_uniformizer]

/-- The convention `∂{u,π}=ū` in multiplicative residue notation. -/
theorem tameValue_unit_uniformizer (d : DiscreteResidueData K k) (u : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) :
    tameValue d (symbol u d.uniformizer) = (d.unitPart (Additive.ofMul u)).toMul := by
  exact congrArg Additive.toMul (tame_unit_uniformizer d u hu)

/-- Reversing the entries gives the inverse residue unit, by the proved skew symmetry. -/
theorem tame_uniformizer_unit (d : DiscreteResidueData K k) (u : Kˣ)
    (hu : d.value (Additive.ofMul u) = 0) :
    tame d (symbol d.uniformizer u) = -d.unitPart (Additive.ofMul u) := by
  rw [symbol_skew, map_neg, tame_unit_uniformizer d u hu]

/-- A field of characteristic `p` has no nontrivial `p`-power root of unity. -/
theorem residueUnit_primePower_eq_one (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : ℕ) (u : kˣ) (hu : u ^ (p ^ r) = 1) : u = 1 := by
  apply Units.ext
  have hpow : (u : k) ^ (p ^ r) = 1 := by
    exact congrArg Units.val hu
  have hzero : ((u : k) - 1) ^ (p ^ r) = 0 := by
    rw [sub_pow_char_pow, hpow, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff'.mp hzero).1

/-- Residue-characteristic-primary torsion has tame value one. -/
theorem tameValue_primePower_torsion (d : DiscreteResidueData K k)
    (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ) (x : K2 K)
    (hx : (p ^ r) • x = 0) : tameValue d x = 1 := by
  apply residueUnit_primePower_eq_one p r
  have ht : (p ^ r) • tame d x = 0 := by rw [← map_nsmul, hx, map_zero]
  exact congrArg Additive.toMul ht

end Quillen.MilnorK2
