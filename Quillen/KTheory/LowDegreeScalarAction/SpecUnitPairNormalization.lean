/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.MilnorNormalization
public import Quillen.KTheory.LowDegreeScalarAction.SpecUnitPairNaturality

/-!
# The same negative normalization on original affine unit-pair pullbacks

Apply original scheme K-pullback first and the target's original kToLowerG map
second. The same lower field normalization then has the negative mapped ordered
symbol value. The residue characteristic-zero premise appears only when the
normalization is applied to the residue field itself.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Quillen.FiniteModuleLocalization

namespace Quillen.LowDegreeScalarAction.SpecUnitPairNormalization

open MilnorNormalization

section FieldTarget
variable {R : CommRingCat.{u}} [IsNoetherianRing R]
  (L : Type u) [Field L] [CharZero L] (f : R →+* L)

/-- Original K-pullback, then target kToLowerG, then the same N gives the negative symbol. -/
theorem pullback_unitPair_negative_milnor (a b : Rˣ) :
    lowerModuleKTwoMilnorNegativeEquivCharZero L
      (Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of L) 2
        (Scheme.pullbackK (Spec.map (CommRingCat.ofHom f)) 2
          (SpecUnitPairs.unitPair R a b)))) =
      -MilnorK.symbol ![Units.map f.toMonoidHom a, Units.map f.toMonoidHom b] := by
  rw [SpecUnitPairNaturality.pullback_unitPair_milnor,
    lowerModuleKTwoMilnorNegativeEquivCharZero_milnor]

end FieldTarget

section Field
variable (F : Type u) [Field F] [CharZero F]

/-- The actual original affine field unit pair has the same negative ordered value. -/
theorem unitPair_negative_milnor (a b : Fˣ) :
    lowerModuleKTwoMilnorNegativeEquivCharZero F
      (Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of F) 2
        (SpecUnitPairs.unitPair (CommRingCat.of F) a b))) = -MilnorK.symbol ![a, b] := by
  rw [SpecUnitPairs.kToLowerG_unitPair,
    lowerModuleKTwoMilnorNegativeEquivCharZero_unitProduct]

end Field

section ActualLocalDvr
variable (B : Type u) [CommRing B] [IsDedekindDomain B]
  (p : IsDedekindDomain.HeightOneSpectrum B)
local notation "A" => Localization.AtPrime p.asIdeal
local notation "K₀" => FractionRing (Localization.AtPrime p.asIdeal)
local notation "κ" => p.asIdeal.ResidueField

/-- The original generic pullback has the negative mapped ordered symbol value.
Only the given field algebra and characteristic-zero target are required. -/
theorem generic_unitPair_negative_milnor (K : Type u) [Field K] [CharZero K]
    [Algebra A K] (a b : Aˣ) :
    lowerModuleKTwoMilnorNegativeEquivCharZero K
      (Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of K) 2
        (Scheme.pullbackK (Spec.map (CommRingCat.ofHom (algebraMap A K))) 2
          (SpecUnitPairs.unitPair (CommRingCat.of A) a b)))) =
      -MilnorK.symbol ![Units.map (algebraMap A K).toMonoidHom a,
        Units.map (algebraMap A K).toMonoidHom b] := by
  rw [SpecUnitPairNaturality.generic_unitPair_milnor,
    lowerModuleKTwoMilnorNegativeEquivCharZero_milnor]

/-- The canonical actual fraction field uses the very same negative normalization. -/
theorem canonical_generic_unitPair_negative_milnor [CharZero K₀] (a b : Aˣ) :
    lowerModuleKTwoMilnorNegativeEquivCharZero K₀
      (Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of K₀) 2
        (Scheme.pullbackK (Spec.map (CommRingCat.ofHom (algebraMap A K₀))) 2
          (SpecUnitPairs.unitPair (CommRingCat.of A) a b)))) =
      -MilnorK.symbol ![Units.map (algebraMap A K₀).toMonoidHom a,
        Units.map (algebraMap A K₀).toMonoidHom b] :=
  generic_unitPair_negative_milnor B p K₀ a b

/-- The actual closed pullback uses N on the residue field, with its explicit CharZero premise. -/
theorem closed_unitPair_negative_milnor [CharZero κ] (a b : Aˣ) :
    lowerModuleKTwoMilnorNegativeEquivCharZero κ
      (Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of κ) 2
        (Scheme.pullbackK (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) 2
          (SpecUnitPairs.unitPair (CommRingCat.of A) a b)))) =
      -MilnorK.symbol ![Units.map (IsLocalRing.residue A).toMonoidHom a,
        Units.map (IsLocalRing.residue A).toMonoidHom b] := by
  rw [SpecUnitPairNaturality.closed_unitPair_milnor,
    lowerModuleKTwoMilnorNegativeEquivCharZero_milnor]

end ActualLocalDvr

end Quillen.LowDegreeScalarAction.SpecUnitPairNormalization
