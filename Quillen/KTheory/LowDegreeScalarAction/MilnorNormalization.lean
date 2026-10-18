/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Field.MilnorKTwoEquivalence
public import Quillen.KTheory.LowDegreeScalarAction.MilnorDvrBoundary

/-!
# Negative Milnor normalization in the original lower finite-module model

The positive lower equivalence retains the original forward Milnor comparison.
The negative inverse first uses the canonical comparison of universes, then the
same upper negative inverse. Original local-DVR boundaries keep their native
positive convention; their inverses have the tame value of the negative normalization.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.ExactCategory
open Quillen.FiniteModuleLocalization
open scoped nonZeroDivisors

namespace Quillen.LowDegreeScalarAction.MilnorNormalization

section FieldSigns
variable (F : Type u) [Field F]

private theorem orderedSymbol_reverse (a b : Fˣ) :
    MilnorK.symbol ![b, a] = -MilnorK.symbol ![a, b] := by
  apply (MilnorK.twoEquiv F).injective
  simp only [MilnorK.twoEquiv_symbol, Matrix.cons_val_zero, Matrix.cons_val_one, map_neg]
  exact MilnorK.K2.symbol_skew b a

/-- Reversing the actual lower field product inverts it, by the published positive marking. -/
theorem loweredUnitProduct_reverse (a b : Fˣ) :
    DvrSymbols.loweredUnitProduct F b a = (DvrSymbols.loweredUnitProduct F a b)⁻¹ := by
  have h := congrArg Additive.toMul (MilnorDvrBoundary.milnorToLowerModuleKTwo_pair F b a)
  rw [orderedSymbol_reverse, map_neg, MilnorDvrBoundary.milnorToLowerModuleKTwo_pair] at h
  exact h.symm

end FieldSigns

section Fields
variable (F : Type u) [Field F] [CharZero F]

/-- The positive lower equivalence uses the original upper map and canonical lowering. -/
def milnorLowerModuleKTwoEquivCharZero : MilnorK.K F 2 ≃+ Additive (G F 2) :=
  (Field.milnorUpperModuleKTwoEquivCharZero F).trans
    (((ModuleCat.finiteModuleExactStructure.{u, u} F).smallKUniverseEquiv.{u, u + 1}
      2).symm.toAdditive)

/-- Its forward homomorphism is exactly the existing lower Milnor comparison. -/
theorem milnorLowerModuleKTwoEquivCharZero_toAddMonoidHom :
    (milnorLowerModuleKTwoEquivCharZero F).toAddMonoidHom =
      MilnorDvrBoundary.milnorToLowerModuleKTwo F := rfl

/-- Applying the positive equivalence uses the same original lower map. -/
@[simp] theorem milnorLowerModuleKTwoEquivCharZero_apply (m : MilnorK.K F 2) :
    milnorLowerModuleKTwoEquivCharZero F m =
      MilnorDvrBoundary.milnorToLowerModuleKTwo F m := rfl

/-- Canonical promotion followed by the same upper negative inverse. -/
def lowerModuleKTwoMilnorNegativeEquivCharZero : Additive (G F 2) ≃+ MilnorK.K F 2 :=
  ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallKUniverseEquiv.{u, u + 1}
    2).toAdditive.trans (Field.upperModuleKTwoMilnorNegativeEquivCharZero F)

/-- The lower normalization is the negative of the positive lower inverse. -/
@[simp] theorem lowerModuleKTwoMilnorNegativeEquivCharZero_apply (x : Additive (G F 2)) :
    lowerModuleKTwoMilnorNegativeEquivCharZero F x =
      -((milnorLowerModuleKTwoEquivCharZero F).symm x) := rfl

/-- The original comparison followed by its positive inverse is the identity. -/
theorem milnorLowerModuleKTwoEquivCharZero_symm_milnor (m : MilnorK.K F 2) :
    (milnorLowerModuleKTwoEquivCharZero F).symm
      (MilnorDvrBoundary.milnorToLowerModuleKTwo F m) = m :=
  (milnorLowerModuleKTwoEquivCharZero F).symm_apply_apply m

/-- The positive inverse followed by the same original comparison is the identity. -/
theorem milnorToLowerModuleKTwo_positiveSymm (x : Additive (G F 2)) :
    MilnorDvrBoundary.milnorToLowerModuleKTwo F
      ((milnorLowerModuleKTwoEquivCharZero F).symm x) = x :=
  (milnorLowerModuleKTwoEquivCharZero F).apply_symm_apply x

/-- The same negative inverse sends the original forward image to the negative input. -/
theorem lowerModuleKTwoMilnorNegativeEquivCharZero_milnor (m : MilnorK.K F 2) :
    lowerModuleKTwoMilnorNegativeEquivCharZero F
      (MilnorDvrBoundary.milnorToLowerModuleKTwo F m) = -m := by
  rw [lowerModuleKTwoMilnorNegativeEquivCharZero_apply,
    milnorLowerModuleKTwoEquivCharZero_symm_milnor]

/-- Applying the original comparison after the negative inverse gives the negative class. -/
theorem milnorToLowerModuleKTwo_negativeEquivCharZero (x : Additive (G F 2)) :
    MilnorDvrBoundary.milnorToLowerModuleKTwo F
      (lowerModuleKTwoMilnorNegativeEquivCharZero F x) = -x := by
  rw [lowerModuleKTwoMilnorNegativeEquivCharZero_apply, map_neg,
    milnorToLowerModuleKTwo_positiveSymm]

/-- Negating the same negative inverse recovers every original lower class. -/
theorem milnorToLowerModuleKTwo_neg_negativeEquivCharZero (x : Additive (G F 2)) :
    MilnorDvrBoundary.milnorToLowerModuleKTwo F
      (-lowerModuleKTwoMilnorNegativeEquivCharZero F x) = x := by
  rw [map_neg, milnorToLowerModuleKTwo_negativeEquivCharZero, neg_neg]

/-- The inverse negative normalization is minus the same original forward map. -/
theorem lowerModuleKTwoMilnorNegativeEquivCharZero_symm_apply (m : MilnorK.K F 2) :
    (lowerModuleKTwoMilnorNegativeEquivCharZero F).symm m =
      -(MilnorDvrBoundary.milnorToLowerModuleKTwo F m) := by
  apply (lowerModuleKTwoMilnorNegativeEquivCharZero F).injective
  rw [(lowerModuleKTwoMilnorNegativeEquivCharZero F).apply_symm_apply, map_neg,
    lowerModuleKTwoMilnorNegativeEquivCharZero_milnor, neg_neg]

/-- The actual ordered lower unit product has the negative ordered symbol value. -/
theorem lowerModuleKTwoMilnorNegativeEquivCharZero_unitProduct (a b : Fˣ) :
    lowerModuleKTwoMilnorNegativeEquivCharZero F
      (Additive.ofMul (DvrSymbols.loweredUnitProduct F a b)) = -MilnorK.symbol ![a, b] := by
  rw [← MilnorDvrBoundary.milnorToLowerModuleKTwo_pair,
    lowerModuleKTwoMilnorNegativeEquivCharZero_milnor]

/-- The reverse ordered lower product has the positive forward ordered symbol under N. -/
theorem lowerModuleKTwoMilnorNegativeEquivCharZero_unitProduct_reverse (a b : Fˣ) :
    lowerModuleKTwoMilnorNegativeEquivCharZero F
      (Additive.ofMul (DvrSymbols.loweredUnitProduct F b a)) = MilnorK.symbol ![a, b] := by
  rw [loweredUnitProduct_reverse]
  change lowerModuleKTwoMilnorNegativeEquivCharZero F
    (-Additive.ofMul (DvrSymbols.loweredUnitProduct F a b)) = _
  rw [map_neg, lowerModuleKTwoMilnorNegativeEquivCharZero_unitProduct, neg_neg]

end Fields

section LocalDvr
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
local notation "A" => Localization.AtPrime p.asIdeal
local notation "K₀" => FractionRing (Localization.AtPrime p.asIdeal)
local notation "κ" => p.asIdeal.ResidueField
local instance : IsDiscreteValuationRing A :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R p.ne_bot _

/-- Ordered unit/uniformizer input retains the original positive residue determinant. -/
theorem localDvrBoundary_unit_uniformizer_det {π : A} (hπ : Irreducible π) (a : Aˣ) :
    MilnorDvrBoundary.localBoundaryDet R p
      (DvrSymbols.loweredUnitProduct K₀ (MilnorK.K2.DVR.fieldUnits A K₀ a)
        (MilnorK.K2.DVR.uniformizer (K := K₀) hπ)) = DvrUnitBoundary.residueUnit R p a := by
  rw [DvrSymbols.loweredUnitProduct_field]
  have hu : MilnorK.K2.DVR.uniformizer (K := K₀) hπ =
      DvrUnitBoundary.fractionUniformizerUnit R p hπ := Units.ext rfl
  rw [hu]
  exact DvrUnitBoundary.localDvrBoundary_unit_principal_det R p hπ a

/-- Reverse order inverts that SAME original residue determinant. -/
theorem localDvrBoundary_uniformizer_unit_det {π : A} (hπ : Irreducible π) (a : Aˣ) :
    MilnorDvrBoundary.localBoundaryDet R p
      (DvrSymbols.loweredUnitProduct K₀ (MilnorK.K2.DVR.uniformizer (K := K₀) hπ)
        (MilnorK.K2.DVR.fieldUnits A K₀ a)) = (DvrUnitBoundary.residueUnit R p a)⁻¹ := by
  rw [loweredUnitProduct_reverse, map_inv, localDvrBoundary_unit_uniformizer_det]

section Canonical

/-- The unchanged raw boundary determinant is tame applied to minus the same N-class. -/
theorem localDvrBoundary_raw_negativeNormalization [CharZero K₀] {π : A} (hπ : Irreducible π)
    (x : G K₀ 2) :
    MilnorDvrBoundary.localBoundaryDet R p x =
      MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K₀) hπ)
        (MilnorK.twoEquiv K₀
          (-lowerModuleKTwoMilnorNegativeEquivCharZero K₀ (Additive.ofMul x))) := by
  have h := MilnorDvrBoundary.localDvrBoundary_milnor_det R p hπ
    (-lowerModuleKTwoMilnorNegativeEquivCharZero K₀ (Additive.ofMul x))
  rw [milnorToLowerModuleKTwo_neg_negativeEquivCharZero] at h
  exact h

/-- Inverting that original determinant gives tame of the same N-class. -/
theorem localDvrBoundary_inverse_negativeNormalization [CharZero K₀] {π : A} (hπ : Irreducible π)
    (x : G K₀ 2) :
    (MilnorDvrBoundary.localBoundaryDet R p x)⁻¹ =
      MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K₀) hπ)
        (MilnorK.twoEquiv K₀
          (lowerModuleKTwoMilnorNegativeEquivCharZero K₀ (Additive.ofMul x))) := by
  have h := MilnorDvrBoundary.localDvrBoundary_milnor_det R p hπ
    (lowerModuleKTwoMilnorNegativeEquivCharZero K₀ (Additive.ofMul x))
  rw [milnorToLowerModuleKTwo_negativeEquivCharZero] at h
  change MilnorDvrBoundary.localBoundaryDet R p x⁻¹ = _ at h
  rw [map_inv] at h
  exact h

/-- The tame value of N on the ordered unit/uniformizer product is the inverse residue. -/
theorem localDvrBoundary_unit_uniformizer_negative_tame [CharZero K₀] {π : A}
    (hπ : Irreducible π) (a : Aˣ) :
    MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K₀) hπ)
      (MilnorK.twoEquiv K₀ (lowerModuleKTwoMilnorNegativeEquivCharZero K₀
        (Additive.ofMul (DvrSymbols.loweredUnitProduct K₀
          (MilnorK.K2.DVR.fieldUnits A K₀ a) (MilnorK.K2.DVR.uniformizer (K := K₀) hπ))))) =
      (DvrUnitBoundary.residueUnit R p a)⁻¹ := by
  rw [← localDvrBoundary_inverse_negativeNormalization,
    localDvrBoundary_unit_uniformizer_det]

/-- Reverse order reverses that normalized tame sign and gives the positive residue unit. -/
theorem localDvrBoundary_uniformizer_unit_negative_tame [CharZero K₀] {π : A}
    (hπ : Irreducible π) (a : Aˣ) :
    MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K₀) hπ)
      (MilnorK.twoEquiv K₀ (lowerModuleKTwoMilnorNegativeEquivCharZero K₀
        (Additive.ofMul (DvrSymbols.loweredUnitProduct K₀
          (MilnorK.K2.DVR.uniformizer (K := K₀) hπ) (MilnorK.K2.DVR.fieldUnits A K₀ a))))) =
      DvrUnitBoundary.residueUnit R p a := by
  rw [← localDvrBoundary_inverse_negativeNormalization,
    localDvrBoundary_uniformizer_unit_det, inv_inv]

end Canonical

section GivenFractionField
variable (K : Type u) [Field K] [CharZero K]

/-- The supplied fraction field keeps its original inverse field restriction and raw boundary. -/
theorem localDvrBoundary_raw_negativeNormalization_field
    [Algebra (Localization.AtPrime p.asIdeal) K]
    [IsFractionRing (Localization.AtPrime p.asIdeal) K] {π : A} (hπ : Irreducible π)
    (x : G K 2) :
    MilnorDvrBoundary.givenLocalBoundaryDet R p K x =
      MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K) hπ)
        (MilnorK.twoEquiv K
          (-lowerModuleKTwoMilnorNegativeEquivCharZero K (Additive.ofMul x))) := by
  have h := MilnorDvrBoundary.localDvrBoundary_milnor_field_det R p K hπ
    (-lowerModuleKTwoMilnorNegativeEquivCharZero K (Additive.ofMul x))
  rw [milnorToLowerModuleKTwo_neg_negativeEquivCharZero] at h
  exact h

/-- The corrected supplied-field statement inverts the same original boundary determinant. -/
theorem localDvrBoundary_inverse_negativeNormalization_field
    [Algebra (Localization.AtPrime p.asIdeal) K]
    [IsFractionRing (Localization.AtPrime p.asIdeal) K] {π : A} (hπ : Irreducible π)
    (x : G K 2) :
    (MilnorDvrBoundary.givenLocalBoundaryDet R p K x)⁻¹ =
      MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K) hπ)
        (MilnorK.twoEquiv K
          (lowerModuleKTwoMilnorNegativeEquivCharZero K (Additive.ofMul x))) := by
  have h := MilnorDvrBoundary.localDvrBoundary_milnor_field_det R p K hπ
    (lowerModuleKTwoMilnorNegativeEquivCharZero K (Additive.ofMul x))
  rw [milnorToLowerModuleKTwo_negativeEquivCharZero] at h
  change MilnorDvrBoundary.givenLocalBoundaryDet R p K x⁻¹ = _ at h
  rw [map_inv] at h
  exact h

end GivenFractionField
end LocalDvr

end Quillen.LowDegreeScalarAction.MilnorNormalization
