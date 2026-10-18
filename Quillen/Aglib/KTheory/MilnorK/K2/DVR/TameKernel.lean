/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K2.DVR.Basic
public import Aglib.KTheory.MilnorK.Residue.DVR

/-!
# Unit symbols generate the algebraic Milnor tame kernel

For every actual DVR `R` with fraction field `K`, `unitSymbolSpan` is the
integer span of field symbols whose entries come from `Rˣ`.
`ker_tame_eq_unitSymbolSpan` identifies it with the kernel of the original
Milnor tame map, for every irreducible uniformizer. The chosen-uniformizer
version needs no supplied uniformizer. No residue-cardinality or
characteristic condition is imposed.

Modulo unit pairs, valuation decomposition reduces every class to `{π,u}`.
If `u=1+πa` and `a` is a unit, Steinberg gives `{π,u}=-{-a,u}`. If `a` is a
nonunit, `a-1` is a unit and
`u=(1+π)(1+π(a-1)/(1+π))` reduces to two unit-coefficient cases.
The original ordered tame formula sends `{π,u}` to `ū⁻¹`, proving the kernel
statement without choosing residue-unit lifts.

The ambient `MilnorK.K2.Group` is Aglib's existing integer tensor quotient.
The canonical uniform residue has exactly the corresponding comap kernel
under `MilnorK.twoEquiv`; this uses the supplied `oneEquiv` residue comparison.

Intended upstream module: `Aglib.KTheory.MilnorK.K2.DVR.TameKernel`. The
hypotheses are `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`,
`[Field K] [Algebra R K] [IsFractionRing R K]`. The current consumer is
Quillen's low-degree field and actual-DVR boundary comparison. This algebraic
statement does not assert actual Quillen K₂ of `R` injects into field K₂,
identify its image, or provide a marked product or same-μ comparison.
-/
@[expose] public section

noncomputable section

namespace MilnorK.K2.DVR

open IsLocalRing

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The integer span of actual field symbols of two ring units. -/
def unitSymbolSpan : Submodule ℤ (Group K) :=
  Submodule.span ℤ {z | ∃ a b : Rˣ, z = symbol (fieldUnits R K a) (fieldUnits R K b)}

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- Each original field symbol of ring units lies in the unit-symbol span. -/
lemma unit_pair_mem (a b : Rˣ) :
    symbol (fieldUnits R K a) (fieldUnits R K b) ∈ unitSymbolSpan R K :=
  Submodule.subset_span ⟨a, b, rfl⟩

variable {R K}

/-- The actual tame map vanishes on the unit-symbol span. -/
lemma unitSymbolSpan_le_ker {π : R} (hπ : Irreducible π) :
    unitSymbolSpan R K ≤ (tame (data (K := K) hπ)).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨a, b, rfl⟩
  exact tame_units (data hπ) _ _ (value_fieldUnits R K a) (value_fieldUnits R K b)

private lemma residue_pi_eq_zero {π : R} (hπ : Irreducible π) : IsLocalRing.residue R π = 0 := by
  rw [residue_eq_zero_iff]
  exact hπ.not_isUnit

private def principalUnit {π : R} (hπ : Irreducible π) (a : R) : Rˣ :=
  ((residue_ne_zero_iff_isUnit (1 + π * a)).mp (by simp [residue_pi_eq_zero hπ])).unit

private lemma principalUnit_spec {π : R} (hπ : Irreducible π) (a : R) :
    (principalUnit hπ a : R) = 1 + π * a := IsUnit.unit_spec _

omit [IsDomain R] [IsDiscreteValuationRing R] in
private lemma pi_unit_mem_of_unit_coefficient {π : R} (hπ : Irreducible π) (a w : Rˣ)
    (hw : (w : R) = 1 + π * (a : R)) :
    symbol (uniformizer (K := K) hπ) (fieldUnits R K w) ∈ unitSymbolSpan R K := by
  have hs : symbol (uniformizer (K := K) hπ * fieldUnits R K (-a))
      (fieldUnits R K w) = 0 := by
    apply steinberg
    change algebraMap R K π * algebraMap R K (-(a : R)) + algebraMap R K (w : R) = 1
    rw [hw, map_add, map_one, map_mul, map_neg]
    ring
  rw [symbol_mul_left] at hs
  rw [eq_neg_of_add_eq_zero_left hs]
  exact (unitSymbolSpan R K).neg_mem (unit_pair_mem R K (-a) w)

private lemma pi_principal_mem {π : R} (hπ : Irreducible π) (a : R) (w : Rˣ)
    (hw : (w : R) = 1 + π * a) :
    symbol (uniformizer (K := K) hπ) (fieldUnits R K w) ∈ unitSymbolSpan R K := by
  classical
  by_cases ha : IsUnit a
  · apply pi_unit_mem_of_unit_coefficient hπ ha.unit w
    simpa only [ha.unit_spec] using hw
  · have ha1 : IsUnit (a - 1) := by
      have h := (isUnit_one_sub_self_of_mem_nonunits a ha).neg
      convert h using 1
      ring
    let r : Rˣ := principalUnit hπ 1
    let b : Rˣ := ha1.unit * r⁻¹
    let s : Rˣ := principalUnit hπ (b : R)
    have hr : (r : R) = 1 + π := by simpa [r] using principalUnit_spec hπ 1
    have hs : (s : R) = 1 + π * (b : R) := principalUnit_spec hπ _
    have hprod : w = r * s := by
      apply Units.ext
      change (w : R) = (r : R) * (s : R)
      rw [hs]
      change (w : R) = r.val * (1 + π * (ha1.unit.val * r.inv))
      calc
        (w : R) = (1 + π) + π * (a - 1) := by rw [hw]; ring
        _ = r.val + π * ha1.unit.val := by rw [hr, ha1.unit_spec]
        _ = r.val + π * ha1.unit.val * (r.val * r.inv) := by rw [r.val_inv, mul_one]
        _ = r.val * (1 + π * (ha1.unit.val * r.inv)) := by ring
    rw [hprod, map_mul, symbol_mul_right]
    apply (unitSymbolSpan R K).add_mem
    · apply pi_unit_mem_of_unit_coefficient hπ 1 r
      simpa using hr
    · exact pi_unit_mem_of_unit_coefficient hπ b s hs

/-- A uniformizer paired with a principal ring unit is generated by unit pairs. -/
lemma pi_unit_mem_of_residue_one {π : R} (hπ : Irreducible π) (w : Rˣ)
    (hw : Units.map (IsLocalRing.residue R).toMonoidHom w = 1) :
    symbol (uniformizer (K := K) hπ) (fieldUnits R K w) ∈ unitSymbolSpan R K := by
  have hres : IsLocalRing.residue R (w : R) = 1 := congrArg Units.val hw
  have hm : (w : R) - 1 ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simp [hres]
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  obtain ⟨a, ha⟩ := hm
  apply pi_principal_mem hπ a w
  linear_combination ha

private lemma symbol_zpow_left (a b : Kˣ) (n : ℤ) :
    symbol (a ^ n) b = n • symbol a b := by
  change symbolBilinear K (Additive.ofMul (a ^ n)) (Additive.ofMul b) = _
  rw [ofMul_zpow, map_smul]
  rfl

private lemma symbol_zpow_right (a b : Kˣ) (n : ℤ) :
    symbol a (b ^ n) = n • symbol a b := by
  change symbolBilinear K (Additive.ofMul a) (Additive.ofMul (b ^ n)) = _
  rw [ofMul_zpow, map_smul]
  rfl

private lemma field_unit_decomposition {π : R} (hπ : Irreducible π) (a : Kˣ) :
    ∃ n : ℤ, ∃ u : Rˣ, a = uniformizer (K := K) hπ ^ n * fieldUnits R K u := by
  refine ⟨value R K (Additive.ofMul a), normalizedLift hπ a, ?_⟩
  rw [normalizedLift_spec]
  dsimp [normalizedUnit]
  rw [mul_left_comm, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

private def piClass {π : R} (hπ : Irreducible π) :
    Additive Rˣ →ₗ[ℤ] (Group K ⧸ unitSymbolSpan R K) :=
  (((unitSymbolSpan R K).mkQ).comp
    (symbolBilinear K (Additive.ofMul (uniformizer (K := K) hπ)))).comp
      ((fieldUnits R K).toAdditive.toIntLinearMap)

private lemma piClass_surjective {π : R} (hπ : Irreducible π) :
    Function.Surjective (piClass (K := K) hπ) := by
  let U := unitSymbolSpan R K
  let q := U.mkQ
  let H := piClass (K := K) hπ
  let S := H.range.comap q
  have hpu (u : Rˣ) : symbol (uniformizer (K := K) hπ) (fieldUnits R K u) ∈ S :=
    ⟨Additive.ofMul u, rfl⟩
  have hup (u : Rˣ) : symbol (fieldUnits R K u) (uniformizer (K := K) hπ) ∈ S := by
    rw [symbol_skew]
    exact S.neg_mem (hpu u)
  have huv (u v : Rˣ) : symbol (fieldUnits R K u) (fieldUnits R K v) ∈ S := by
    change q _ ∈ H.range
    have hz : q (symbol (fieldUnits R K u) (fieldUnits R K v)) = 0 :=
      (Submodule.Quotient.mk_eq_zero U).mpr (unit_pair_mem R K u v)
    rw [hz]
    exact H.range.zero_mem
  have hpp : symbol (uniformizer (K := K) hπ) (uniformizer (K := K) hπ) ∈ S := by
    rw [symbol_self]
    have he : (-1 : Kˣ) = fieldUnits R K (-1) := Units.ext (by simp [fieldUnits])
    rw [he]
    exact hpu (-1)
  have hsymbol (a b : Kˣ) : symbol a b ∈ S := by
    obtain ⟨m, u, ha⟩ := field_unit_decomposition hπ a
    obtain ⟨n, v, hb⟩ := field_unit_decomposition hπ b
    rw [ha, hb, symbol_mul_left, symbol_mul_right, symbol_mul_right,
      symbol_zpow_left, symbol_zpow_left, symbol_zpow_right, symbol_zpow_right]
    exact S.add_mem
      (S.add_mem (S.smul_mem m (S.smul_mem n hpp)) (S.smul_mem m (hpu v)))
      (S.add_mem (S.smul_mem n (hup u)) (huv u v))
  have hall (x : Group K) : x ∈ S := by
    refine Submodule.Quotient.induction_on (steinbergSpan K) x ?_
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => exact hsymbol a.toMul b.toMul
    | add a b ha hb => exact S.add_mem ha hb
  intro z
  obtain ⟨x, rfl⟩ := U.mkQ_surjective z
  exact hall x

private def tameOnUnitQuotient {π : R} (hπ : Irreducible π) :
    (Group K ⧸ unitSymbolSpan R K) →ₗ[ℤ] UnitsAdd (ResidueField R) :=
  (unitSymbolSpan R K).liftQ (tame (data hπ)) (unitSymbolSpan_le_ker hπ)

private lemma tameOnUnitQuotient_piClass {π : R} (hπ : Irreducible π) (u : Rˣ) :
    tameOnUnitQuotient (K := K) hπ (piClass (K := K) hπ (Additive.ofMul u)) =
      -Additive.ofMul (Units.map (IsLocalRing.residue R).toMonoidHom u) := by
  change tame (data hπ) (symbol (uniformizer (K := K) hπ) (fieldUnits R K u)) = _
  calc
    _ = -(data (K := K) hπ).unitPart (Additive.ofMul (fieldUnits R K u)) :=
      tame_uniformizer_unit (data hπ) _ (value_fieldUnits R K u)
    _ = _ := by
      change -Additive.ofMul (unitResidue hπ (fieldUnits R K u)) = _
      rw [unitResidue_fieldUnits]

/-- Unit pairs generate the actual Milnor tame kernel over every DVR. -/
theorem ker_tame_eq_unitSymbolSpan {π : R} (hπ : Irreducible π) :
    (tame (data (K := K) hπ)).ker = unitSymbolSpan R K := by
  apply le_antisymm _ (unitSymbolSpan_le_ker hπ)
  intro x hx
  obtain ⟨u, hu⟩ := piClass_surjective hπ ((unitSymbolSpan R K).mkQ x)
  have hz : -Additive.ofMul (Units.map (IsLocalRing.residue R).toMonoidHom u.toMul) = 0 := by
    calc
      _ = tameOnUnitQuotient (K := K) hπ (piClass (K := K) hπ u) :=
        (tameOnUnitQuotient_piClass hπ u.toMul).symm
      _ = tameOnUnitQuotient (K := K) hπ ((unitSymbolSpan R K).mkQ x) :=
        congrArg (tameOnUnitQuotient hπ) hu
      _ = 0 := hx
  have hres : Units.map (IsLocalRing.residue R).toMonoidHom u.toMul = 1 :=
    congrArg Additive.toMul (neg_eq_zero.mp hz)
  have humem := pi_unit_mem_of_residue_one (K := K) hπ u.toMul hres
  have hu0 : piClass (K := K) hπ u = 0 :=
    (Submodule.Quotient.mk_eq_zero (unitSymbolSpan R K)).mpr humem
  exact (Submodule.Quotient.mk_eq_zero (unitSymbolSpan R K)).mp (hu.symm.trans hu0)

/-- The same kernel statement for the original multiplicative tame value. -/
theorem tameValue_eq_one_iff_unitSymbolSpan {π : R} (hπ : Irreducible π) (x : Group K) :
    tameValue (data (K := K) hπ) x = 1 ↔ x ∈ unitSymbolSpan R K := by
  rw [← ker_tame_eq_unitSymbolSpan hπ]
  change (tame (data (K := K) hπ) x).toMul = 1 ↔ tame (data (K := K) hπ) x = 0
  constructor
  · intro h
    exact Additive.toMul.injective h
  · intro h
    simp [h]

variable (R K) in
/-- Kernel generation for the actual DVR constructor with its chosen uniformizer. -/
theorem ker_chosenTame_eq_unitSymbolSpan :
    (tame (chosenData R K)).ker = unitSymbolSpan R K :=
  ker_tame_eq_unitSymbolSpan (IsDiscreteValuationRing.exists_irreducible R).choose_spec

end MilnorK.K2.DVR

namespace MilnorK.DVR

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The canonical uniform degree-two residue has the original unit-symbol-span kernel. -/
theorem ker_residue_one_eq_unitSymbolSpan_comap :
    (residue R K 1).ker =
      (MilnorK.K2.DVR.unitSymbolSpan R K).comap (twoEquiv K).toLinearMap := by
  ext x
  change residue R K 1 x = 0 ↔
    twoEquiv K x ∈ MilnorK.K2.DVR.unitSymbolSpan R K
  rw [← MilnorK.K2.DVR.ker_chosenTame_eq_unitSymbolSpan R K]
  change residue R K 1 x = 0 ↔
    MilnorK.K2.tame (MilnorK.K2.DVR.chosenData R K) (twoEquiv K x) = 0
  rw [← oneEquiv_residue_one R K x]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply (oneEquiv (IsLocalRing.ResidueField R)).injective
    simpa only [map_zero] using h

/-- Vanishing of the canonical uniform residue is membership in the original unit span. -/
theorem residue_one_eq_zero_iff_mem_unitSymbolSpan (x : MilnorK.K K 2) :
    residue R K 1 x = 0 ↔
      twoEquiv K x ∈ MilnorK.K2.DVR.unitSymbolSpan R K := by
  change x ∈ (residue R K 1).ker ↔ _
  rw [ker_residue_one_eq_unitSymbolSpan_comap R K]
  rfl

end MilnorK.DVR
