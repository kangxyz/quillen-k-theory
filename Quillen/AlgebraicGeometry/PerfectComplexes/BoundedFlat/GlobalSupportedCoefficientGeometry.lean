/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterGeometry
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientOpenRestriction
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseCanonicalRow

/-!
# The integral Spec row as a natural isomorphism of actual open pairs

The two original row symmetries give an isomorphism of the original coefficient open pair
with the parameter-first product open pair. Its opposite is natural for every actual
integral coefficient map. No quasi-compactness assumption or replacement support is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedParameter
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The original coefficient open pairs and their complete coefficient squares. -/
def coefficientPairs : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ Scheme.OpenPairs.{u}ᵒᵖ where
  obj a := op (boundedFlatCoefficientOpenPair f a)
  map g := (boundedFlatCoefficientOpenPairMap f g).op
  map_id a := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op P, a)
    · exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op Q, a)
  map_comp g h := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact coefficientMap_comp P g h
    · exact coefficientMap_comp Q g h

/-- Both actual row symmetries form the original open-pair square. -/
def coefficientPairIso (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    boundedFlatCoefficientOpenPair f a ≅ pair f.left (Spec a.right) :=
  Scheme.openPairProperty.isoMk
    (Arrow.isoMk (canonicalRowIso P a) (canonicalRowIso Q a)
      (canonicalRowIso_scheme f a).symm)

/-- The open corner is exactly the prescribed row symmetry. -/
theorem coefficientPairIso_hom_left (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (coefficientPairIso f a).hom.hom.left = (canonicalRowIso P a).hom := rfl

/-- The ambient corner is exactly the prescribed row symmetry. -/
theorem coefficientPairIso_hom_right (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (coefficientPairIso f a).hom.hom.right = (canonicalRowIso Q a).hom := rfl

/-- Opposite row symmetry goes from parameter support to original coefficient support. -/
def coefficientPairsIso :
    specUnder ⋙ (pairs f.left).op ≅ coefficientPairs f :=
  NatIso.ofComponents (fun a => (coefficientPairIso f a).op) (by
    intro a b g
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact (canonicalRowIso_coefficient P g).symm
    · exact (canonicalRowIso_coefficient Q g).symm)

end Quillen.PerfectComplexes.GlobalSupportedParameter
