/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.SpecUnitPairNormalization

/-!
# Original-map clients for lower Milnor normalization

These clients retain the literal upper negative inverse, original scheme pullback,
and original raw local-DVR boundary expressions. Generation is reused with its
actual residue-section premise and supplies no extra premise to the boundary clients.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.ExactCategory AlgebraicGeometry
open Quillen.FiniteModuleLocalization

namespace Quillen.LowDegreeScalarAction.MilnorNormalization.Clients

/-- Original lower recovery literally promotes to the original upper negative inverse first. -/
theorem original_lower_recovery (F : Type u) [Field F] [CharZero F] (x : G F 2) :
    MilnorDvrBoundary.milnorToLowerModuleKTwo F
      (-Field.upperModuleKTwoMilnorNegativeEquivCharZero F
        (Additive.ofMul
          ((ModuleCat.finiteModuleExactStructure.{u, u} F).smallKUniverseEquiv.{u, u + 1}
          2 x))) = Additive.ofMul x := by
  have h := milnorToLowerModuleKTwo_neg_negativeEquivCharZero F (Additive.ofMul x)
  simpa only [lowerModuleKTwoMilnorNegativeEquivCharZero, AddEquiv.trans_apply,
    MulEquiv.toAdditive_apply_apply, toMul_ofMul] using h

/-- A concrete non-field source: actual affine pullback from integer unit pairs to rationals. -/
theorem integer_affine_pullback (a b : ℤˣ) :
    lowerModuleKTwoMilnorNegativeEquivCharZero ℚ
      (Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of ℚ) 2
        (Scheme.pullbackK (Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))) 2
          (SpecUnitPairs.unitPair (CommRingCat.of ℤ) a b)))) =
      -MilnorK.symbol ![Units.map (Int.castRingHom ℚ).toMonoidHom a,
        Units.map (Int.castRingHom ℚ).toMonoidHom b] :=
  SpecUnitPairNormalization.pullback_unitPair_negative_milnor
    (R := CommRingCat.of ℤ) ℚ (Int.castRingHom ℚ) a b

section ActualLocalDvr
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
local notation "A" => Localization.AtPrime p.asIdeal
local notation "K₀" => FractionRing (Localization.AtPrime p.asIdeal)
local notation "κ" => p.asIdeal.ResidueField
local instance : IsDiscreteValuationRing A :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R p.ne_bot _

/-- An arbitrary actual lower class under the original canonical raw boundary and determinant. -/
theorem original_canonical_boundary [CharZero K₀] {π : A} (hπ : Irreducible π)
    (x : G K₀ 2) :
    (Field.moduleDetEquiv κ
      ((ModuleCat.finiteModuleExactStructure.{u, u} κ).smallKUniverseEquiv.{u, u + 1} 1
        (DedekindLocalDvr.localDvrBoundary R p 1 x)))⁻¹ =
      MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K₀) hπ)
        (MilnorK.twoEquiv K₀
          (lowerModuleKTwoMilnorNegativeEquivCharZero K₀ (Additive.ofMul x))) :=
  localDvrBoundary_inverse_negativeNormalization R p hπ x

/-- The supplied-field client retains the original inverse field restriction before the boundary. -/
theorem original_given_boundary (K : Type u) [Field K] [CharZero K]
    [Algebra (Localization.AtPrime p.asIdeal) K]
    [IsFractionRing (Localization.AtPrime p.asIdeal) K] {π : A} (hπ : Irreducible π)
    (x : G K 2) :
    (Field.moduleDetEquiv κ
      ((ModuleCat.finiteModuleExactStructure.{u, u} κ).smallKUniverseEquiv.{u, u + 1} 1
        (DedekindLocalDvr.localDvrBoundary R p 1
          ((DvrUnitBoundary.fractionFieldRestrictionExact R p K).smallKMap.{u} 2 x))))⁻¹ =
      MilnorK.K2.tameValue (MilnorK.K2.DVR.data (K := K) hπ)
        (MilnorK.twoEquiv K
          (lowerModuleKTwoMilnorNegativeEquivCharZero K (Additive.ofMul x))) :=
  localDvrBoundary_inverse_negativeNormalization_field R p K hπ x

/-- A genuine residue section gives literal coefficient cancellation after original K-pullback. -/
theorem residue_section_closed_normalization [CharZero κ]
    (s : κ →+* A) (hs : (IsLocalRing.residue A).comp s = RingHom.id κ) (a b : κˣ) :
    lowerModuleKTwoMilnorNegativeEquivCharZero κ
      (Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of κ) 2
        (Scheme.pullbackK (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) 2
          (SpecUnitPairs.unitPair (CommRingCat.of A)
            (Units.map s.toMonoidHom a) (Units.map s.toMonoidHom b))))) =
      -MilnorK.symbol ![a, b] := by
  have hunit (c : κˣ) :
      Units.map (IsLocalRing.residue A).toMonoidHom (Units.map s.toMonoidHom c) = c := by
    apply Units.ext
    exact congrArg (fun f : κ →+* κ => f (c : κ)) hs
  have h := SpecUnitPairNormalization.closed_unitPair_negative_milnor R p
    (Units.map s.toMonoidHom a) (Units.map s.toMonoidHom b)
  rw [hunit, hunit] at h
  exact h

end ActualLocalDvr

end Quillen.LowDegreeScalarAction.MilnorNormalization.Clients
