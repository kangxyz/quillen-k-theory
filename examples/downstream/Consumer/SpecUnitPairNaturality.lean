/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.LowDegreeScalarAction.SpecUnitPairNaturality
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Algebra.Field.ZMod

/-!
# Original generic and closed scheme K-pullback values

The actual algebra and residue maps preserve the positive ordered pair. Closed
consumers use vector-bundle K-pullback followed by the field comparison.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory Polynomial AlgebraicGeometry
open Quillen.LowDegreeScalarAction

namespace SpecUnitPairNaturalityClients

/-- The actual affine-line origin at zero over the coefficient field. -/
def origin (F : Type u) [Field F] : IsDedekindDomain.HeightOneSpectrum F[X] where
  asIdeal := Ideal.span {X - C (0 : F)}
  isPrime := Ideal.IsMaximal.isPrime
    (PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C 0))
  ne_bot := by simp

/-- The supplied field retains its literal algebra map; no fraction-ring premise is needed. -/
theorem rationalOrigin_givenField (K : Type) [Field K]
    [Algebra (Localization.AtPrime (origin ℚ).asIdeal) K]
    (a b : (Localization.AtPrime (origin ℚ).asIdeal)ˣ) :
    Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of K) 2
      (Scheme.pullbackK (Spec.map (CommRingCat.ofHom
        (algebraMap (Localization.AtPrime (origin ℚ).asIdeal) K))) 2
          (SpecUnitPairs.unitPair (CommRingCat.of (Localization.AtPrime (origin ℚ).asIdeal))
            a b))) =
      MilnorDvrBoundary.milnorToLowerModuleKTwo K
        (MilnorK.symbol ![
          Units.map (algebraMap (Localization.AtPrime (origin ℚ).asIdeal) K).toMonoidHom a,
          Units.map (algebraMap (Localization.AtPrime (origin ℚ).asIdeal) K).toMonoidHom b]) :=
  SpecUnitPairNaturality.generic_unitPair_milnor.{0} ℚ[X] (origin ℚ) K a b

/-- The original canonical fraction ring is a concrete instance of the same generic arrow. -/
theorem rationalOrigin_canonicalGeneric
    (a b : (Localization.AtPrime (origin ℚ).asIdeal)ˣ) :
    Additive.ofMul (SpecUnitPairs.kToLowerG
      (CommRingCat.of (FractionRing (Localization.AtPrime (origin ℚ).asIdeal))) 2
        (Scheme.pullbackK (Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.AtPrime (origin ℚ).asIdeal)
            (FractionRing (Localization.AtPrime (origin ℚ).asIdeal))))) 2
              (SpecUnitPairs.unitPair
                (CommRingCat.of (Localization.AtPrime (origin ℚ).asIdeal)) a b))) =
      MilnorDvrBoundary.milnorToLowerModuleKTwo
        (FractionRing (Localization.AtPrime (origin ℚ).asIdeal))
        (MilnorK.symbol ![
          Units.map (algebraMap (Localization.AtPrime (origin ℚ).asIdeal)
            (FractionRing (Localization.AtPrime (origin ℚ).asIdeal))).toMonoidHom a,
          Units.map (algebraMap (Localization.AtPrime (origin ℚ).asIdeal)
            (FractionRing (Localization.AtPrime (origin ℚ).asIdeal))).toMonoidHom b]) :=
  rationalOrigin_givenField (FractionRing (Localization.AtPrime (origin ℚ).asIdeal)) a b

/-- The actual closed K-pullback equals the genuine pair on the actual residue field. -/
theorem rationalOrigin_closed_pair
    (a b : (Localization.AtPrime (origin ℚ).asIdeal)ˣ) :
    Scheme.pullbackK (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Localization.AtPrime (origin ℚ).asIdeal)))) 2
        (SpecUnitPairs.unitPair (CommRingCat.of (Localization.AtPrime (origin ℚ).asIdeal))
          a b) =
      SpecUnitPairs.unitPair (CommRingCat.of (origin ℚ).asIdeal.ResidueField)
        (Units.map (IsLocalRing.residue (Localization.AtPrime (origin ℚ).asIdeal)).toMonoidHom a)
        (Units.map (IsLocalRing.residue (Localization.AtPrime (origin ℚ).asIdeal)).toMonoidHom b) :=
  SpecUnitPairNaturality.pullback_unitPair_field.{0} (R :=
    CommRingCat.of (Localization.AtPrime (origin ℚ).asIdeal))
      (origin ℚ).asIdeal.ResidueField
      (IsLocalRing.residue (Localization.AtPrime (origin ℚ).asIdeal)) a b

/-- Original K is pulled back before applying target-only KToG and affine comparison. -/
theorem origin_closed_milnor (F : Type u) [Field F]
    (a b : (Localization.AtPrime (origin F).asIdeal)ˣ) :
    Additive.ofMul (SpecUnitPairs.kToLowerG (CommRingCat.of (origin F).asIdeal.ResidueField) 2
      (Scheme.pullbackK (Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue (Localization.AtPrime (origin F).asIdeal)))) 2
          (SpecUnitPairs.unitPair (CommRingCat.of (Localization.AtPrime (origin F).asIdeal))
            a b))) =
      MilnorDvrBoundary.milnorToLowerModuleKTwo (origin F).asIdeal.ResidueField
        (MilnorK.symbol ![
          Units.map (IsLocalRing.residue (Localization.AtPrime (origin F).asIdeal)).toMonoidHom a,
          Units.map (IsLocalRing.residue
            (Localization.AtPrime (origin F).asIdeal)).toMonoidHom b]) :=
  SpecUnitPairNaturality.closed_unitPair_milnor F[X] (origin F) a b

example (a b : (Localization.AtPrime (origin (ZMod 2)).asIdeal)ˣ) :
    Additive.ofMul (SpecUnitPairs.kToLowerG
      (CommRingCat.of (origin (ZMod 2)).asIdeal.ResidueField) 2
        (Scheme.pullbackK (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
          (Localization.AtPrime (origin (ZMod 2)).asIdeal)))) 2
            (SpecUnitPairs.unitPair
              (CommRingCat.of (Localization.AtPrime (origin (ZMod 2)).asIdeal)) a b))) =
      MilnorDvrBoundary.milnorToLowerModuleKTwo (origin (ZMod 2)).asIdeal.ResidueField
        (MilnorK.symbol ![Units.map (IsLocalRing.residue
          (Localization.AtPrime (origin (ZMod 2)).asIdeal)).toMonoidHom a,
            Units.map (IsLocalRing.residue
              (Localization.AtPrime (origin (ZMod 2)).asIdeal)).toMonoidHom b]) :=
  origin_closed_milnor (ZMod 2) a b

example (a b : (Localization.AtPrime (origin (ZMod 3)).asIdeal)ˣ) :
    Scheme.pullbackK (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
      (Localization.AtPrime (origin (ZMod 3)).asIdeal)))) 2
        (SpecUnitPairs.unitPair
          (CommRingCat.of (Localization.AtPrime (origin (ZMod 3)).asIdeal)) a b) =
      SpecUnitPairs.unitPair (CommRingCat.of (origin (ZMod 3)).asIdeal.ResidueField)
        (Units.map (IsLocalRing.residue
          (Localization.AtPrime (origin (ZMod 3)).asIdeal)).toMonoidHom a)
        (Units.map (IsLocalRing.residue
          (Localization.AtPrime (origin (ZMod 3)).asIdeal)).toMonoidHom b) :=
  SpecUnitPairNaturality.pullback_unitPair_field.{0} (R :=
    CommRingCat.of (Localization.AtPrime (origin (ZMod 3)).asIdeal))
      (origin (ZMod 3)).asIdeal.ResidueField
      (IsLocalRing.residue (Localization.AtPrime (origin (ZMod 3)).asIdeal)) a b

end SpecUnitPairNaturalityClients
