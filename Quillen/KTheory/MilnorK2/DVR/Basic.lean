/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.MilnorK2.Residue
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Actual DVR data for the Milnor tame map

For a mathlib DVR `R`, its fraction field `K`, and an irreducible uniformizer,
this module constructs the original `DiscreteResidueData`. The valuation is
mathlib's maximal-ideal valuation; the integer order and normalized-unit
lifts adapt that existing API to the Milnor tame formula. This introduces no
independent generic valuation construction.

The value, residue-unit homomorphism, normalization and Steinberg input
identities are proved from the actual DVR and fraction-ring instances.
`chosenData` chooses a uniformizer whose existence follows from the DVR.
This is algebraic tame-symbol data only: Quillen K₂ of the DVR, its injection
or generation, and product marking are outside this module's scope.

Migrated definitions and proofs: R5
`Aglib/RingTheory/DiscreteValuationRing/UnitPart.lean`, SHA-256
`68b775a58e5e560ebdab9cd667d5c6551140bad0e087eb48b8676900e3c433c4`,
and `Aglib/RingTheory/DiscreteValuationRing/ResidueData.lean`, SHA-256
`1ec099edf73e7489c42c9bcbbaeb593c6457eddafd1cf6a78150934524b6c9b6`.
The actual maps and all DVR/fraction-field conditions are retained.
-/
@[expose] public section

namespace Quillen.MilnorK2.DVR

open scoped WithZero
open IsLocalRing

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual maximal-ideal valuation on the fraction field of `R`. -/
noncomputable def valuation : Valuation K ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal R).valuation K

/-- Integer order with the convention that an irreducible uniformizer has value one. -/
noncomputable def value : UnitsAdd K →ₗ[ℤ] ℤ :=
  ({ toFun := fun a => -WithZero.log (valuation R K (a.toMul : K))
     map_zero' := by simp
     map_add' := by
       intro a b
       change -WithZero.log (valuation R K ((a.toMul : K) * b.toMul)) = _
       rw [map_mul, WithZero.log_mul ((map_ne_zero (valuation R K)).mpr a.toMul.ne_zero)
         ((map_ne_zero (valuation R K)).mpr b.toMul.ne_zero), neg_add] } :
    UnitsAdd K →+ ℤ).toIntLinearMap

theorem value_apply (a : Kˣ) :
    value R K (Additive.ofMul a) = -WithZero.log (valuation R K (a : K)) := rfl

theorem valuation_ne_zero (a : Kˣ) : valuation R K (a : K) ≠ 0 :=
  (map_ne_zero (valuation R K)).mpr a.ne_zero

theorem valuation_neg_one : valuation R K (-1 : K) = 1 := by simp

@[simp] theorem value_neg_one : value R K (Additive.ofMul (-1 : Kˣ)) = 0 := by
  simp [value_apply]

theorem value_eq_zero_iff (a : Kˣ) :
    value R K (Additive.ofMul a) = 0 ↔ valuation R K (a : K) = 1 := by
  rw [value_apply, neg_eq_zero]
  constructor
  · intro h
    have := WithZero.exp_log (valuation_ne_zero R K a)
    simpa [h] using this.symm
  · intro h
    simp [h]

theorem value_pos_iff (a : Kˣ) :
    0 < value R K (Additive.ofMul a) ↔ valuation R K (a : K) < 1 := by
  rw [value_apply, neg_pos, WithZero.log_lt_iff_lt_exp (valuation_ne_zero R K a)]
  simp

theorem valuation_unit (u : Rˣ) :
    valuation R K (algebraMap R K (u : R)) = 1 := by
  simp [valuation, IsDiscreteValuationRing.maximalIdeal]

/-- Ring units embedded into fraction-field units. -/
def fieldUnits : Rˣ →* Kˣ := Units.map (algebraMap R K).toMonoidHom

@[simp] theorem value_fieldUnits (u : Rˣ) :
    value R K (Additive.ofMul (fieldUnits R K u)) = 0 := by
  rw [value_apply]
  change -WithZero.log (valuation R K (algebraMap R K (u : R))) = 0
  rw [valuation_unit, WithZero.log_one, neg_zero]

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem fieldUnits_injective : Function.Injective (fieldUnits R K) := by
  intro a b h
  apply Units.ext
  apply IsFractionRing.injective R K
  exact congrArg Units.val h

variable {R K}

/-- An irreducible of `R` as a genuine nonzero fraction-field unit. -/
noncomputable def uniformizer {π : R} (hπ : Irreducible π) : Kˣ :=
  Units.mk0 (algebraMap R K π) (by simpa using hπ.ne_zero)

theorem valuation_uniformizer {π : R} (hπ : Irreducible π) :
    valuation R K (uniformizer (K := K) hπ : K) = WithZero.exp (-1 : ℤ) := by
  change (IsDiscreteValuationRing.maximalIdeal R).valuation K (algebraMap R K π) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (IsDiscreteValuationRing.maximalIdeal R).intValuation_singleton hπ.ne_zero
    hπ.maximalIdeal_eq

@[simp] theorem value_uniformizer {π : R} (hπ : Irreducible π) :
    value R K (Additive.ofMul (uniformizer (K := K) hπ)) = 1 := by
  rw [value_apply, valuation_uniformizer hπ, WithZero.log_exp]
  rfl

/-- The multiplicative normalization `a ↦ a * π ^ (-v(a))`. -/
noncomputable def normalizedUnit {π : R} (hπ : Irreducible π) : Kˣ →* Kˣ where
  toFun a := a * uniformizer (K := K) hπ ^ (-value R K (Additive.ofMul a))
  map_one' := by simp
  map_mul' a b := by
    change a * b * uniformizer (K := K) hπ ^
      (-value R K (Additive.ofMul a + Additive.ofMul b)) = _
    rw [map_add, neg_add, zpow_add]
    ac_rfl

theorem value_normalizedUnit {π : R} (hπ : Irreducible π) (a : Kˣ) :
    value R K (Additive.ofMul (normalizedUnit (K := K) hπ a)) = 0 := by
  change value R K (Additive.ofMul a +
    (-value R K (Additive.ofMul a)) • Additive.ofMul (uniformizer (K := K) hπ)) = 0
  simp

theorem exists_normalizedUnit_lift {π : R} (hπ : Irreducible π) (a : Kˣ) :
    ∃ u : Rˣ, fieldUnits R K u = normalizedUnit (K := K) hπ a := by
  have hval := (value_eq_zero_iff R K _).mp (value_normalizedUnit hπ a)
  have hm : (normalizedUnit (K := K) hπ a : K) ∈
      MonoidHom.mker (valuation R K) := hval
  rw [valuation, IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid] at hm
  obtain ⟨r, hr, heq⟩ := hm
  refine ⟨hr.unit, Units.ext ?_⟩
  simpa [fieldUnits, hr.unit_spec] using heq

/-- The unique ring-unit lift of the normalized fraction-field element. -/
noncomputable def normalizedLift {π : R} (hπ : Irreducible π) : Kˣ →* Rˣ where
  toFun a := (exists_normalizedUnit_lift hπ a).choose
  map_one' := by
    apply fieldUnits_injective R K
    rw [(exists_normalizedUnit_lift hπ 1).choose_spec, map_one, map_one]
  map_mul' a b := by
    apply fieldUnits_injective R K
    rw [(exists_normalizedUnit_lift hπ (a * b)).choose_spec, map_mul, map_mul,
      (exists_normalizedUnit_lift hπ a).choose_spec,
      (exists_normalizedUnit_lift hπ b).choose_spec]

theorem normalizedLift_spec {π : R} (hπ : Irreducible π) (a : Kˣ) :
    fieldUnits R K (normalizedLift (K := K) hπ a) = normalizedUnit (K := K) hπ a :=
  (exists_normalizedUnit_lift hπ a).choose_spec

/-- Normalizing an embedded ring unit returns that same ring unit. -/
@[simp] theorem normalizedLift_fieldUnits {π : R} (hπ : Irreducible π) (u : Rˣ) :
    normalizedLift (K := K) hπ (fieldUnits R K u) = u := by
  apply fieldUnits_injective R K
  rw [normalizedLift_spec]
  change fieldUnits R K u * uniformizer (K := K) hπ ^
    (-value R K (Additive.ofMul (fieldUnits R K u))) = fieldUnits R K u
  simp

/-- Actual reduction of the normalized ring unit in the residue field. -/
noncomputable def unitResidue {π : R} (hπ : Irreducible π) :
    Kˣ →* (ResidueField R)ˣ :=
  (Units.map (residue R).toMonoidHom).comp (normalizedLift (K := K) hπ)

/-- The residue-unit homomorphism agrees with the residue map on ring units. -/
@[simp] theorem unitResidue_fieldUnits {π : R} (hπ : Irreducible π) (u : Rˣ) :
    unitResidue (K := K) hπ (fieldUnits R K u) =
      Units.map (residue R).toMonoidHom u := by
  simp [unitResidue]

/-- The normalized residue map in additive notation, linear over the integers. -/
noncomputable def unitPart {π : R} (hπ : Irreducible π) :
    UnitsAdd K →ₗ[ℤ] UnitsAdd (ResidueField R) :=
  (unitResidue (K := K) hπ).toAdditive.toIntLinearMap

theorem normalizedLift_coe_of_value_zero {π : R} (hπ : Irreducible π) (a : Kˣ)
    (ha : value R K (Additive.ofMul a) = 0) :
    algebraMap R K (normalizedLift (K := K) hπ a : R) = (a : K) := by
  have h := congrArg Units.val (normalizedLift_spec hπ a)
  simpa [fieldUnits, normalizedUnit, ha] using h

theorem unitResidue_coe_of_value_zero {π : R} (hπ : Irreducible π) (a : Kˣ)
    (ha : value R K (Additive.ofMul a) = 0) (r : R)
    (hr : algebraMap R K r = (a : K)) :
    (unitResidue (K := K) hπ a : ResidueField R) = residue R r := by
  have heq : (normalizedLift (K := K) hπ a : R) = r :=
    IsFractionRing.injective R K ((normalizedLift_coe_of_value_zero hπ a ha).trans hr.symm)
  change residue R (normalizedLift (K := K) hπ a : R) = _
  rw [heq]

@[simp] theorem unitResidue_uniformizer {π : R} (hπ : Irreducible π) :
    unitResidue (K := K) hπ (uniformizer (K := K) hπ) = 1 := by
  have heq : normalizedLift (K := K) hπ (uniformizer (K := K) hπ) = 1 := by
    apply fieldUnits_injective R K
    rw [normalizedLift_spec, map_one]
    simp [normalizedUnit]
  simp [unitResidue, heq]

@[simp] theorem unitPart_uniformizer {π : R} (hπ : Irreducible π) :
    unitPart (K := K) hπ (Additive.ofMul (uniformizer (K := K) hπ)) = 0 := by
  change Additive.ofMul (unitResidue hπ (uniformizer (K := K) hπ)) = 0
  rw [unitResidue_uniformizer]
  rfl

@[simp] theorem unitPart_neg_one {π : R} (hπ : Irreducible π) :
    unitPart (K := K) hπ (Additive.ofMul (-1 : Kˣ)) = residueSign (ResidueField R) := by
  change Additive.ofMul (unitResidue hπ (-1 : Kˣ)) =
    Additive.ofMul (-1 : (ResidueField R)ˣ)
  congr 1
  apply Units.ext
  rw [unitResidue_coe_of_value_zero hπ (-1) (value_neg_one R K) (-1) (by simp)]
  simp

/-- Positive order in `a+b=1` forces `b` to be a unit reducing to one. -/
theorem positive {π : R} (hπ : Irreducible π) (a b : Kˣ)
    (hab : (a : K) + (b : K) = 1) (ha : 0 < value R K (Additive.ofMul a)) :
    value R K (Additive.ofMul b) = 0 ∧ unitPart (K := K) hπ (Additive.ofMul b) = 0 := by
  have hva : valuation R K (a : K) < 1 := (value_pos_iff R K a).mp ha
  have hba : (b : K) = 1 - (a : K) := by linear_combination hab
  have hvb : valuation R K (b : K) = 1 := by
    rw [hba, (valuation R K).map_sub_eq_of_lt_left (by simpa using hva), map_one]
  have hb : value R K (Additive.ofMul b) = 0 := (value_eq_zero_iff R K b).mpr hvb
  obtain ⟨ra, hra⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hva.le
  have hrzero : residue R ra = 0 := by
    apply (residue_eq_zero_iff _).mpr
    exact ((IsDiscreteValuationRing.maximalIdeal R).valuation_lt_one_iff_mem
      (K := K) ra).mp (by simpa only [valuation, hra] using hva)
  have hsum : ra + (normalizedLift (K := K) hπ b : R) = 1 := by
    apply IsFractionRing.injective R K
    rw [map_add, map_one, hra, normalizedLift_coe_of_value_zero hπ b hb]
    exact hab
  have hres : (unitResidue (K := K) hπ b : ResidueField R) = 1 := by
    change residue R (normalizedLift (K := K) hπ b : R) = 1
    simpa only [map_add, map_one, hrzero, zero_add] using congrArg (residue R) hsum
  refine ⟨hb, ?_⟩
  change Additive.ofMul (unitResidue hπ b) = 0
  rw [show unitResidue (K := K) hπ b = 1 from Units.ext hres]
  rfl

/-- Negative order in `a+b=1` gives equal orders and opposite normalized residues. -/
theorem negative {π : R} (hπ : Irreducible π) (a b : Kˣ)
    (hab : (a : K) + (b : K) = 1) (ha : value R K (Additive.ofMul a) < 0) :
    value R K (Additive.ofMul b) = value R K (Additive.ofMul a) ∧
      unitPart (K := K) hπ (Additive.ofMul b) =
        unitPart (K := K) hπ (Additive.ofMul a) + residueSign (ResidueField R) := by
  let c : Kˣ := (-1) * b / a
  have hsum : ((a⁻¹ : Kˣ) : K) + (c : K) = 1 := by
    simp only [c, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val, Units.val_mul,
      Units.val_neg, Units.val_one]
    field_simp
    linear_combination -hab
  have hainv : 0 < value R K (Additive.ofMul a⁻¹) := by
    rw [ofMul_inv, map_neg]
    exact neg_pos.mpr ha
  obtain ⟨hcv, hcu⟩ := positive hπ a⁻¹ c hsum hainv
  simp only [c, ofMul_div, ofMul_mul, map_sub, map_add,
    value_neg_one, zero_add] at hcv
  simp only [c, ofMul_div, ofMul_mul, map_sub, map_add,
    unitPart_neg_one] at hcu
  refine ⟨sub_eq_zero.mp hcv, sub_eq_zero.mp ?_⟩
  calc
    unitPart (K := K) hπ (Additive.ofMul b) -
        (unitPart (K := K) hπ (Additive.ofMul a) + residueSign (ResidueField R)) =
      (residueSign (ResidueField R) + unitPart (K := K) hπ (Additive.ofMul b) -
        unitPart (K := K) hπ (Additive.ofMul a)) -
        (residueSign (ResidueField R) + residueSign (ResidueField R)) := by abel
    _ = 0 := by rw [hcu, residueSign_add_self, sub_self]

open scoped WithZero
open IsLocalRing

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

variable {R K}

/-- Residue data constructed entirely from an actual DVR and its fraction field. -/
noncomputable def data {π : R} (hπ : Irreducible π) :
    DiscreteResidueData K (ResidueField R) where
  value := value R K
  unitPart := unitPart (K := K) hπ
  uniformizer := uniformizer (K := K) hπ
  value_uniformizer := value_uniformizer hπ
  unitPart_uniformizer := unitPart_uniformizer hπ
  unitPart_neg_one := unitPart_neg_one hπ
  positive := positive hπ
  negative := negative hπ

/-- Zero-order entries reduce the actual ring equation `a+b=1` in the residue field. -/
theorem unitReductionCompatible {π : R} (hπ : Irreducible π) :
    UnitReductionCompatible (data (K := K) hπ) := by
  intro a b hab ha hb
  change (unitResidue (K := K) hπ a : ResidueField R) +
    (unitResidue (K := K) hπ b : ResidueField R) = 1
  have hsum : (normalizedLift (K := K) hπ a : R) +
      (normalizedLift (K := K) hπ b : R) = 1 := by
    apply IsFractionRing.injective R K
    rw [map_add, map_one, normalizedLift_coe_of_value_zero hπ a ha,
      normalizedLift_coe_of_value_zero hπ b hb]
    exact hab
  change residue R (normalizedLift (K := K) hπ a : R) +
    residue R (normalizedLift (K := K) hπ b : R) = 1
  simpa only [map_add, map_one] using congrArg (residue R) hsum

variable (R K) in
/-- A DVR constructor choosing a uniformizer whose existence follows from the DVR instance. -/
noncomputable def chosenData : DiscreteResidueData K (ResidueField R) :=
  data (K := K) (IsDiscreteValuationRing.exists_irreducible R).choose_spec

variable (R K) in
/-- The chosen-uniformizer constructor satisfies the reduction compatibility theorem. -/
theorem chosenData_unitReductionCompatible : UnitReductionCompatible (chosenData R K) :=
  unitReductionCompatible (K := K) (IsDiscreteValuationRing.exists_irreducible R).choose_spec

end Quillen.MilnorK2.DVR
