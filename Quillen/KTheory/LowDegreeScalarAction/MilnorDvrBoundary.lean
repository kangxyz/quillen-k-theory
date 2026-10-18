/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Field.PositiveSymbolMarking
public import Quillen.KTheory.LowDegreeScalarAction.DvrUnitBoundary
public import Quillen.KTheory.Field.MilnorKTwoSurjectivity
public import Quillen.KTheory.Plus.StableFiberPerfectness
public import Quillen.Aglib.KTheory.MilnorK.K2.DVR.TameKernel
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Original local-DVR boundary of the actual Milnor comparison

The original upper Milnor map is lowered through the canonical comparison of
universes of the same finite-module category. Its surjectivity uses proved
stable-fiber perfectness and all-rank Steinberg kernel generation. Positive
ordered-pair marking supplies its literal ring-unit-product value.

The original local-DVR boundary, followed by canonical residue promotion and
the original determinant, is the actual Milnor tame map. The proof uses the
proved unit-symbol description of its kernel and the positive ordered
unit/uniformizer boundary. No Matsumoto injectivity, residue-size condition,
or reverse-order calibration is needed.

-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory
open Quillen.FiniteModuleLocalization
open scoped nonZeroDivisors

namespace Quillen.LowDegreeScalarAction.MilnorDvrBoundary

section Fields
variable (F : Type u) [Field F]

/-- The original upper Milnor comparison followed by the canonical lower-model map. -/
def milnorToLowerModuleKTwo : MilnorK.K F 2 →+ Additive (G F 2) :=
  let e := (ModuleCat.finiteModuleExactStructure.{u, u} F).smallKUniverseEquiv.{u, u + 1} 2
  e.symm.toAdditive.toAddMonoidHom.comp (Field.milnorToUpperModuleKTwo F)

/-- Surjectivity is supplied by proved fiber perfectness and genuine kernel generation. -/
theorem milnorToLowerModuleKTwo_surjective :
    Function.Surjective (milnorToLowerModuleKTwo F) := by
  let : Group.IsPerfect (FiniteProjectiveModule.StableCompletion.StableFiberPiOne F) :=
    FiniteProjectiveModule.StableCompletion.stableFiberPiOne_isPerfect F
  exact (((ModuleCat.finiteModuleExactStructure.{u, u} F).smallKUniverseEquiv.{u, u + 1}
    2).symm.toAdditive.surjective).comp
      (Field.milnorToUpperModuleKTwo_surjective_of_fiberPerfect F)

/-- Actual ordered pairs retain the canonically lowered original field product. -/
theorem milnorToLowerModuleKTwo_pair (a b : Fˣ) :
    milnorToLowerModuleKTwo F (MilnorK.symbol ![a, b]) =
      Additive.ofMul (DvrSymbols.loweredUnitProduct F a b) := by
  unfold milnorToLowerModuleKTwo
  rw [AddMonoidHom.comp_apply,
    Field.milnorToUpperModuleKTwo_pair_eq_unitProduct,
    DvrSymbols.loweredUnitProduct_field]
  rfl

/-- The same actual comparison on Aglib's original degree-two tensor quotient. -/
def tensorMilnorToLowerModuleKTwo : MilnorK.K2.Group F →ₗ[ℤ] Additive (G F 2) :=
  ((milnorToLowerModuleKTwo F).comp (MilnorK.twoEquiv F).symm.toAddMonoidHom).toIntLinearMap

/-- The original tensor-quotient comparison cancels its own canonical degree-two equivalence. -/
theorem tensorMilnorToLowerModuleKTwo_twoEquiv (m : MilnorK.K F 2) :
    tensorMilnorToLowerModuleKTwo F (MilnorK.twoEquiv F m) =
      milnorToLowerModuleKTwo F m := by
  change milnorToLowerModuleKTwo F ((MilnorK.twoEquiv F).symm (MilnorK.twoEquiv F m)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The original tensor symbol has the same literal ordered-product value. -/
theorem tensorMilnorToLowerModuleKTwo_symbol (a b : Fˣ) :
    tensorMilnorToLowerModuleKTwo F (MilnorK.K2.symbol a b) =
      Additive.ofMul (DvrSymbols.loweredUnitProduct F a b) := by
  change milnorToLowerModuleKTwo F
    ((MilnorK.twoEquiv F).symm (MilnorK.K2.symbol a b)) = _
  rw [MilnorK.twoEquiv_symm_symbol, milnorToLowerModuleKTwo_pair]

end Fields

section LocalDvr
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
local notation "A" => Localization.AtPrime p.asIdeal
local notation "K₀" => FractionRing (Localization.AtPrime p.asIdeal)
local notation "κ" => p.asIdeal.ResidueField
local instance : IsDiscreteValuationRing A :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R p.ne_bot _

/-- The original local boundary followed by canonical promotion and original determinant. -/
def localBoundaryDet : G K₀ 2 →* κˣ :=
  let e := (ModuleCat.finiteModuleExactStructure.{u, u} κ).smallKUniverseEquiv.{u, u + 1} 1
  (Field.moduleDetEquiv κ).toMonoidHom.comp
    (e.toMonoidHom.comp (DedekindLocalDvr.localDvrBoundary R p 1))

private def tensorBoundary : MilnorK.K2.Group K₀ →ₗ[ℤ] Additive κˣ :=
  ((localBoundaryDet R p).toAdditive.toIntLinearMap).comp
    (tensorMilnorToLowerModuleKTwo K₀)

private theorem tensorBoundary_apply (m : MilnorK.K2.Group K₀) :
    tensorBoundary R p m =
      Additive.ofMul (localBoundaryDet R p (tensorMilnorToLowerModuleKTwo K₀ m).toMul) := by
  simp only [tensorBoundary, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
    MonoidHom.coe_toAdditive, Function.comp_apply]

private theorem tensorBoundary_unit_unit (a b : Aˣ) :
    tensorBoundary R p
      (MilnorK.K2.symbol (MilnorK.K2.DVR.fieldUnits A K₀ a)
        (MilnorK.K2.DVR.fieldUnits A K₀ b)) = 0 := by
  rw [tensorBoundary_apply, tensorMilnorToLowerModuleKTwo_symbol,
    DvrSymbols.loweredUnitProduct_field]
  dsimp only [localBoundaryDet, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    toMul_ofMul, MilnorK.K2.DVR.fieldUnits]
  rw [DvrSymbols.localDvrBoundary_unit_unit, map_one, map_one]
  rfl

private theorem unitSymbolSpan_le_tensorBoundary_ker :
    MilnorK.K2.DVR.unitSymbolSpan A K₀ ≤ (tensorBoundary R p).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨a, b, rfl⟩
  exact tensorBoundary_unit_unit R p a b

private theorem tensorBoundary_unit_uniformizer {π : A} (hπ : Irreducible π) (a : Aˣ) :
    tensorBoundary R p
      (MilnorK.K2.symbol (MilnorK.K2.DVR.fieldUnits A K₀ a)
        (MilnorK.K2.DVR.uniformizer (K := K₀) hπ)) =
      Additive.ofMul (DvrUnitBoundary.residueUnit R p a) := by
  rw [tensorBoundary_apply, tensorMilnorToLowerModuleKTwo_symbol,
    DvrSymbols.loweredUnitProduct_field, toMul_ofMul]
  unfold localBoundaryDet
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hu : MilnorK.K2.DVR.uniformizer (K := K₀) hπ =
      DvrUnitBoundary.fractionUniformizerUnit R p hπ := Units.ext rfl
  rw [hu]
  dsimp only [MilnorK.K2.DVR.fieldUnits]
  apply congrArg Additive.ofMul
  exact DvrUnitBoundary.localDvrBoundary_unit_principal_det R p hπ a

private theorem tame_unit_uniformizer {π : A} (hπ : Irreducible π) (a : Aˣ) :
    MilnorK.K2.tame (MilnorK.K2.DVR.data (K := K₀) hπ)
      (MilnorK.K2.symbol (MilnorK.K2.DVR.fieldUnits A K₀ a)
        (MilnorK.K2.DVR.uniformizer (K := K₀) hπ)) =
      Additive.ofMul (DvrUnitBoundary.residueUnit R p a) := by
  have h := MilnorK.K2.tame_unit_uniformizer (MilnorK.K2.DVR.data (K := K₀) hπ)
    (MilnorK.K2.DVR.fieldUnits A K₀ a) (MilnorK.K2.DVR.value_fieldUnits A K₀ a)
  change MilnorK.K2.tame (MilnorK.K2.DVR.data (K := K₀) hπ)
    (MilnorK.K2.symbol _ (MilnorK.K2.DVR.uniformizer (K := K₀) hπ)) = _ at h
  rw [h]
  change Additive.ofMul
    (MilnorK.K2.DVR.unitResidue (K := K₀) hπ (MilnorK.K2.DVR.fieldUnits A K₀ a)) = _
  rw [MilnorK.K2.DVR.unitResidue_fieldUnits]
  rfl

/-- The original determinant of the native local boundary is the actual tame value. -/
theorem localDvrBoundary_tensorMilnor_det {π : A} (hπ : Irreducible π)
    (m : MilnorK.K2.Group K₀) :
    localBoundaryDet R p (tensorMilnorToLowerModuleKTwo K₀ m).toMul =
      MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K₀) hπ) m := by
  let t := MilnorK.K2.tame (MilnorK.K2.DVR.data (K := K₀) hπ)
  obtain ⟨a, ha⟩ := IsLocalRing.surjective_units_map_of_local_ringHom
    (IsLocalRing.residue A) IsLocalRing.residue_surjective inferInstance (t m).toMul
  let s := MilnorK.K2.symbol (MilnorK.K2.DVR.fieldUnits A K₀ a)
    (MilnorK.K2.DVR.uniformizer (K := K₀) hπ)
  have hts : t s = t m := by
    rw [tame_unit_uniformizer R p hπ a]
    exact congrArg Additive.ofMul ha
  have hker : m - s ∈ MilnorK.K2.DVR.unitSymbolSpan A K₀ := by
    rw [← MilnorK.K2.DVR.ker_tame_eq_unitSymbolSpan hπ]
    change t (m - s) = 0
    rw [map_sub, hts, sub_self]
  have hb : tensorBoundary R p (m - s) = 0 :=
    unitSymbolSpan_le_tensorBoundary_ker R p hker
  rw [map_sub, sub_eq_zero] at hb
  have hsa := tensorBoundary_unit_uniformizer R p hπ a
  have hta := tame_unit_uniformizer R p hπ a
  dsimp only [s] at hb
  conv at hb => rhs; rw [hsa]
  rw [← hta, hts] at hb
  rw [tensorBoundary_apply] at hb
  exact congrArg Additive.toMul hb

/-- The same compatibility retains the original uniform degree-two Milnor group. -/
theorem localDvrBoundary_milnor_det {π : A} (hπ : Irreducible π)
    (m : MilnorK.K K₀ 2) :
    localBoundaryDet R p (milnorToLowerModuleKTwo K₀ m).toMul =
      MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K₀) hπ) (MilnorK.twoEquiv K₀ m) := by
  have h := localDvrBoundary_tensorMilnor_det R p hπ (MilnorK.twoEquiv K₀ m)
  rw [tensorMilnorToLowerModuleKTwo_twoEquiv] at h
  exact h

section GivenFractionField
variable (K : Type u) [Field K] [Algebra (Localization.AtPrime p.asIdeal) K]
  [IsFractionRing (Localization.AtPrime p.asIdeal) K]

/-- The supplied field retains the original canonical inverse field-restriction map. -/
def givenLocalBoundaryDet : G K 2 →* κˣ :=
  (localBoundaryDet R p).comp
    ((DvrUnitBoundary.fractionFieldRestrictionExact R p K).smallKMap.{u} 2)

private def givenTensorBoundary : MilnorK.K2.Group K →ₗ[ℤ] Additive κˣ :=
  ((givenLocalBoundaryDet R p K).toAdditive.toIntLinearMap).comp
    (tensorMilnorToLowerModuleKTwo K)

private theorem givenTensorBoundary_apply (m : MilnorK.K2.Group K) :
    givenTensorBoundary R p K m =
      Additive.ofMul (givenLocalBoundaryDet R p K
        (tensorMilnorToLowerModuleKTwo K m).toMul) := by
  simp only [givenTensorBoundary, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
    MonoidHom.coe_toAdditive, Function.comp_apply]

private theorem given_coefficient (a : Aˣ) :
    Units.map (DedekindLocalDvr.localFractionFieldEquiv R p K).toRingEquiv.symm.toMonoidHom
        (MilnorK.K2.DVR.fieldUnits A K a) = MilnorK.K2.DVR.fieldUnits A K₀ a := by
  apply Units.ext
  exact (DedekindLocalDvr.localFractionFieldEquiv R p K).symm.commutes (a : A)

private theorem givenTensorBoundary_unit_unit (a b : Aˣ) :
    givenTensorBoundary R p K
      (MilnorK.K2.symbol (MilnorK.K2.DVR.fieldUnits A K a)
        (MilnorK.K2.DVR.fieldUnits A K b)) = 0 := by
  rw [givenTensorBoundary_apply, tensorMilnorToLowerModuleKTwo_symbol, toMul_ofMul]
  dsimp only [givenLocalBoundaryDet, MonoidHom.comp_apply]
  change Additive.ofMul (localBoundaryDet R p
    ((DvrUnitBoundary.ringTransportExact
      (DedekindLocalDvr.localFractionFieldEquiv R p K).toRingEquiv.symm).smallKMap.{u} 2
        (DvrSymbols.loweredUnitProduct K _ _))) = 0
  rw [DvrUnitBoundary.loweredUnitProduct_ringIso, given_coefficient, given_coefficient]
  have h := tensorBoundary_unit_unit R p a b
  rw [tensorBoundary_apply, tensorMilnorToLowerModuleKTwo_symbol, toMul_ofMul] at h
  exact h

private theorem givenUnitSymbolSpan_le_boundary_ker :
    MilnorK.K2.DVR.unitSymbolSpan A K ≤ (givenTensorBoundary R p K).ker := by
  apply Submodule.span_le.mpr
  rintro z ⟨a, b, rfl⟩
  exact givenTensorBoundary_unit_unit R p K a b

private theorem givenTensorBoundary_unit_uniformizer {π : A} (hπ : Irreducible π)
    (a : Aˣ) :
    givenTensorBoundary R p K
      (MilnorK.K2.symbol (MilnorK.K2.DVR.fieldUnits A K a)
        (MilnorK.K2.DVR.uniformizer (K := K) hπ)) =
      Additive.ofMul (DvrUnitBoundary.residueUnit R p a) := by
  rw [givenTensorBoundary_apply, tensorMilnorToLowerModuleKTwo_symbol,
    DvrSymbols.loweredUnitProduct_field, toMul_ofMul]
  have hu : MilnorK.K2.DVR.uniformizer (K := K) hπ =
      DvrUnitBoundary.givenUniformizerUnit R p hπ K := Units.ext rfl
  rw [hu]
  dsimp only [givenLocalBoundaryDet, localBoundaryDet, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MilnorK.K2.DVR.fieldUnits]
  exact congrArg Additive.ofMul
    (DvrUnitBoundary.localDvrBoundary_unit_principal_field_det R p hπ K a)

private theorem given_tame_unit_uniformizer {π : A} (hπ : Irreducible π) (a : Aˣ) :
    MilnorK.K2.tame (MilnorK.K2.DVR.data (K := K) hπ)
      (MilnorK.K2.symbol (MilnorK.K2.DVR.fieldUnits A K a)
        (MilnorK.K2.DVR.uniformizer (K := K) hπ)) =
      Additive.ofMul (DvrUnitBoundary.residueUnit R p a) := by
  have h := MilnorK.K2.tame_unit_uniformizer (MilnorK.K2.DVR.data (K := K) hπ)
    (MilnorK.K2.DVR.fieldUnits A K a) (MilnorK.K2.DVR.value_fieldUnits A K a)
  change MilnorK.K2.tame (MilnorK.K2.DVR.data (K := K) hπ)
    (MilnorK.K2.symbol _ (MilnorK.K2.DVR.uniformizer (K := K) hπ)) = _ at h
  rw [h]
  change Additive.ofMul
    (MilnorK.K2.DVR.unitResidue (K := K) hπ (MilnorK.K2.DVR.fieldUnits A K a)) = _
  rw [MilnorK.K2.DVR.unitResidue_fieldUnits]
  rfl

/-- For a supplied actual fraction field, original inverse field restriction
retains the actual tame value under the original local boundary and determinant. -/
theorem localDvrBoundary_tensorMilnor_field_det {π : A} (hπ : Irreducible π)
    (m : MilnorK.K2.Group K) :
    givenLocalBoundaryDet R p K (tensorMilnorToLowerModuleKTwo K m).toMul =
      MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K) hπ) m := by
  let t := MilnorK.K2.tame (MilnorK.K2.DVR.data (K := K) hπ)
  obtain ⟨a, ha⟩ := IsLocalRing.surjective_units_map_of_local_ringHom
    (IsLocalRing.residue A) IsLocalRing.residue_surjective inferInstance (t m).toMul
  let s := MilnorK.K2.symbol (MilnorK.K2.DVR.fieldUnits A K a)
    (MilnorK.K2.DVR.uniformizer (K := K) hπ)
  have hts : t s = t m := by
    rw [given_tame_unit_uniformizer R p K hπ a]
    exact congrArg Additive.ofMul ha
  have hker : m - s ∈ MilnorK.K2.DVR.unitSymbolSpan A K := by
    rw [← MilnorK.K2.DVR.ker_tame_eq_unitSymbolSpan hπ]
    change t (m - s) = 0
    rw [map_sub, hts, sub_self]
  have hb : givenTensorBoundary R p K (m - s) = 0 :=
    givenUnitSymbolSpan_le_boundary_ker R p K hker
  rw [map_sub, sub_eq_zero] at hb
  have hsa := givenTensorBoundary_unit_uniformizer R p K hπ a
  have hta := given_tame_unit_uniformizer R p K hπ a
  dsimp only [s] at hb
  conv at hb => rhs; rw [hsa]
  rw [← hta, hts] at hb
  rw [givenTensorBoundary_apply] at hb
  exact congrArg Additive.toMul hb

/-- The supplied-field statement on the original uniform degree-two Milnor group. -/
theorem localDvrBoundary_milnor_field_det {π : A} (hπ : Irreducible π)
    (m : MilnorK.K K 2) :
    givenLocalBoundaryDet R p K (milnorToLowerModuleKTwo K m).toMul =
      MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K) hπ) (MilnorK.twoEquiv K m) := by
  have h := localDvrBoundary_tensorMilnor_field_det R p K hπ (MilnorK.twoEquiv K m)
  rw [tensorMilnorToLowerModuleKTwo_twoEquiv] at h
  exact h

end GivenFractionField

end LocalDvr

end Quillen.LowDegreeScalarAction.MilnorDvrBoundary
